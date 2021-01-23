#include <assert.h>
#include <err.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>

#include "pset.h"

struct literal {
	struct literal *next;
	unsigned mark;
	int name;
};

struct clause {
	struct clause *next;
	struct pset *literals;
	unsigned mark;
	int sat;
};

struct cnf {
	struct literal *lbuf;
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

		while (c != NULL && c->mark >= mark) {
			cnf->clauses[i] = c->next;
			pset_refdown(c->literals);
			free(c);
			c = cnf->clauses[i];
		}
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
		if (sat(cnf, mark + 1))
			return 1;
	}
	assert(cnf->t == l);
	cnf->t = l->next;
	unwind(cnf, mark);

	/* next, try setting to 'false' */
	l->next = cnf->f;
	cnf->f = l;

	if (try_set(cnf, mark, -l->name)) {
		if (sat(cnf, mark + 1))
			return 1;
	}
	assert(cnf->f == l);
	cnf->f = l->next;

	l->next = cnf->z;
	cnf->z = l;

	return 0;
}

static struct cnf *dimacs_header(FILE *f)
{
	struct cnf *result;
	unsigned nvars, nclauses;
	int rc;

	rc = fscanf(f, " p cnf %u %u ", &nvars, &nclauses);
	if (rc != 2)
		errx(EXIT_FAILURE, "failed parsing dimacs header");

	result = calloc(1, sizeof(*result) + nclauses * sizeof(struct clause *));
	if (result == NULL)
		err(EXIT_FAILURE, "malloc: cnf: %u %u", nvars, nclauses);

	result->nvars = nvars;
	result->nclauses = nclauses;

	return result;
}

static struct clause *dimacs_clause(FILE *f)
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
	}

	return result;
}

static struct cnf *dimacs(FILE *f)
{
	struct cnf *result;
	size_t i;

	result = dimacs_header(f);

	for (i = 0; i < result->nclauses; i++)
		result->clauses[i] = dimacs_clause(f);

	result->lbuf = calloc(result->nvars, sizeof(*result->lbuf));
	if (result->lbuf == NULL)
		err(EXIT_FAILURE, "calloc: lbuf");

	for (i = 0; i < result->nvars; i++) {
		struct literal *l = result->lbuf + i;
		l->next = result->z;
		l->mark = 0;
		l->name = i + 1;
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

	free(cnf->lbuf);
	free(cnf);

	return rc;
}
