#include <assert.h>
#include <err.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>

#include "pset.h"

struct count {
	int literal;
	unsigned count;
};

struct literal {
	struct literal *next;
	unsigned mark;
	unsigned count;
	int name;
};

struct clause {
	struct clause *next;
	struct pset *literals;
	unsigned mark;
	int sat;
};

struct cnf {
	struct count *counts;
	struct literal *z;
	struct literal *t;
	struct literal *f;
	size_t nvars;
	size_t nclauses;
	struct clause *clauses[];
	/* TODO cache unsatisfied clauses */
};

static void unwind(struct cnf *cnf, unsigned mark)
{
	size_t i;

	for (i = 0; i < cnf->nclauses; i++) {
		struct clause *c;

		c = cnf->clauses[i];
		assert(c != NULL);

		if (c->mark != mark)
			continue;

		cnf->clauses[i] = c->next;
		pset_refdown(c->literals);
		free(c);
	}
}

static int satisfied(const struct cnf *cnf)
{
	size_t i;

	for (i = 0; i < cnf->nclauses; i++) {
		assert(cnf->clauses[i] != NULL);
		if (!cnf->clauses[i]->sat)
			return 0;
	}

	return 1;
}

static int try_set(struct cnf *cnf, unsigned mark, int l)
{
	size_t i;

	for (i = 0; i < cnf->nclauses; i++) {
		struct clause *c;

		c = cnf->clauses[i];
		assert(c != NULL);

		if (c->sat)
			continue;

		if (pset_contains(c->literals, l)) {
			/* the clause is satisfied */
			struct clause *n;

			n = malloc(sizeof(*n));
			if (n == NULL)
				err(EXIT_FAILURE, "malloc: clause");

			n->next = c;
			n->literals = c->literals;
			pset_refup(c->literals);
			n->mark = mark;
			n->sat = 1;
			cnf->clauses[i] = n;
		} else if (pset_contains(c->literals, -l)) {
			/* another literal in the clause in not satisfied */
			struct pset *p;
			struct clause *n;

			p = pset_remove(c->literals, -l);
			/* c is unsatisfiable */
			if (p == NULL)
				return 0;

			n = malloc(sizeof(*n));
			if (n == NULL)
				err(EXIT_FAILURE, "malloc: clause");

			n->next = c;
			n->literals = p;
			n->mark = mark;
			n->sat = 0;
			cnf->clauses[i] = n;
		}
	}

	return 1;
}

static int sat(struct cnf *cnf, unsigned mark)
{
	struct literal *l;

	if (satisfied(cnf))
		return 1;
	else if (cnf->z == NULL)
		return 0;

	l = cnf->z;
	cnf->z = l->next;
	l->mark = mark;
	assert(l->name >= 0);

	/* first, try setting to 'true' */
	l->next = cnf->t;
	cnf->t = l;

	if (try_set(cnf, mark, l->name)) {
		if (sat(cnf, mark + 1)) {
			unwind(cnf, mark);
			return 1;
		}
	}
	assert(cnf->t == l);
	cnf->t = l->next;
	unwind(cnf, mark);

	/* next, try setting to 'false' */
	l->next = cnf->f;
	cnf->f = l;

	if (try_set(cnf, mark, -l->name)) {
		if (sat(cnf, mark + 1)) {
			unwind(cnf, mark);
			return 1;
		}
	}
	assert(cnf->f == l);
	cnf->f = l->next;
	unwind(cnf, mark);

	l->next = cnf->z;
	cnf->z = l;

	return 0;
}

static struct cnf *dimacs_header(FILE *f)
{
	struct cnf *result;
	struct count *counts;
	unsigned nvars, nclauses;
	int rc;
	unsigned i;

	rc = fscanf(f, " p cnf %u %u ", &nvars, &nclauses);
	if (rc != 2)
		errx(EXIT_FAILURE, "failed parsing dimacs header");

	result = calloc(1, sizeof(*result) + nclauses * sizeof(struct clause *));
	if (result == NULL)
		err(EXIT_FAILURE, "malloc: cnf: %u %u", nvars, nclauses);

	result->nvars = nvars;
	result->nclauses = nclauses;

	counts = calloc(nvars + 1, sizeof(*counts));
	if (counts == NULL)
		err(EXIT_FAILURE, "malloc: counts");

	for (i = 0; i <= nvars; i++)
		counts[i].literal = i;
	result->counts = counts;

	return result;
}

static struct clause *dimacs_clause(FILE *f, struct count *counts)
{
	struct clause *result;

	result = calloc(1, sizeof(*result));
	if (result == NULL)
		err(EXIT_FAILURE, "malloc: clause");

	for (;;) {
		int literal;
		int rc;

		rc = fscanf(f, " %d ", &literal);
		if (rc != 1)
			errx(EXIT_FAILURE, "failed parsing clause");

		if (literal == 0)
			break;

		result->literals = pset_insert(result->literals, literal);

		if (literal < 0)
			counts[-literal].count++;
		else
			counts[literal].count++;
	}

	return result;
}

static int count_cmp(const void *_a, const void *_b)
{
	const struct count *a = _a;
	const struct count *b = _b;

	return a->count - b->count;
}

static struct cnf *dimacs(FILE *f)
{
	struct cnf *result;
	size_t i;

	result = dimacs_header(f);

	for (i = 0; i < result->nclauses; i++)
		result->clauses[i] = dimacs_clause(f, result->counts);

	qsort(result->counts, result->nvars + 1, sizeof(struct count),
	      count_cmp);

	for (i = 0; i <= result->nvars; i++) {
		struct literal *l;

		if (result->counts[i].literal == 0)
			continue;

		l = malloc(sizeof(*l));
		if (l == NULL)
			err(EXIT_FAILURE, "malloc: literal");

		l->next = result->z;
		l->mark = 0;
		l->name = result->counts[i].literal;
		l->count = result->counts[i].count;
		result->z = l;
	}

	return result;
}

static void print_list(const struct literal *l)
{
	const struct literal *i;

	for (i = l; i != NULL; i = i->next) {
		printf("  %d\n", i->name);
	}
}

int main()
{
	struct literal *l;
	struct cnf *cnf;
	int issat;
	int rc;

	cnf = dimacs(stdin);

	issat = sat(cnf, 1);
	if (issat) {
		printf("satisfied!\n\n");
		if (cnf->t != NULL) {
			printf("true:\n");
			print_list(cnf->t);
		}
		if (cnf->f != NULL) {
			printf("false:\n");
			print_list(cnf->f);
		}
		if (cnf->z != NULL) {
			printf("don't care:\n");
			print_list(cnf->z);
		}
		rc = EXIT_SUCCESS;
	} else {
		assert(cnf->f == NULL);
		assert(cnf->t == NULL);
		printf("unsatisfied\n");
		rc = EXIT_FAILURE;
	}

	unwind(cnf, 0);

	for (l = cnf->z; l != NULL;) {
		struct literal *f = l;
		l = l->next;
		free(f);
	}
	for (l = cnf->t; l != NULL;) {
		struct literal *f = l;
		l = l->next;
		free(f);
	}
	for (l = cnf->f; l != NULL;) {
		struct literal *f = l;
		l = l->next;
		free(f);
	}

	free(cnf->counts);
	free(cnf);

	return rc;
}
