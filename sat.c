#define _POSIX_C_SOURCE 199309L
#include <assert.h>
#include <err.h>
#include <signal.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>

#include "dlist.c"
#include "pset.c"

#define UNUSED(x) (void)(x)

#define containerof(p, str, elt) \
	(str *)(((char *)p) - offsetof(str, elt))

struct literal {
	union {
		struct dl dl;
		struct literal *next;
	} elt;
	size_t *clauses;
	size_t nclauses;
	unsigned mark;
	int name;
};

struct clause {
	struct pset *literals;
	unsigned mark;
	int sat;
};

struct cnf {
	struct list z;
	struct literal *lbuf;
	struct literal *t;
	struct literal *f;
	size_t nvars;
	size_t nclauses;
	struct clause *clauses[];
	/* TODO cache unsatisfied clauses */
};

static void unwind_all(struct cnf *cnf)
{
	size_t i;

	for (i = 0; i < cnf->nclauses; i++) {
		struct clause *c;

		c = cnf->clauses[i];
		assert(c != NULL);

		while (c->mark != 0) {
			pset_refdown(c->literals);
			c -= 1;
		}
		pset_refdown(c->literals);
		free(c);
	}
}

static void unwind(struct cnf *cnf, unsigned mark)
{
	size_t i;

	for (i = 0; i < cnf->nclauses; i++) {
		struct clause *c;

		c = cnf->clauses[i];
		assert(c != NULL);

		while (c->mark >= mark) {
			cnf->clauses[i] = c - 1;
			pset_refdown(c->literals);
			c -= 1;
		}
	}

	while (cnf->f != NULL && cnf->f->mark >= mark) {
		struct literal *f = cnf->f->elt.next;
		list_insert(&cnf->z, &cnf->f->elt.dl);
		cnf->f = f;
	}

	while (cnf->t != NULL && cnf->t->mark >= mark) {
		struct literal *t = cnf->t->elt.next;
		list_insert(&cnf->z, &cnf->t->elt.dl);
		cnf->t = t;
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

static int try_set(struct cnf *cnf, unsigned mark, struct literal *l, int name)
{
	size_t i;

	for (i = 0; i < l->nclauses; i++) {
		struct clause *c;

		c = cnf->clauses[l->clauses[i]];
		assert(c != NULL);

		if (c->sat)
			continue;

		if (pset_contains(c->literals, name)) {
			/* the clause is satisfied */
			struct clause *n = c + 1;

			n->literals = c->literals;
			pset_refup(c->literals);
			n->mark = mark;
			n->sat = 1;
			cnf->clauses[l->clauses[i]] = n;
		} else if (pset_contains(c->literals, -name)) {
			/* another literal in the clause is not satisfied */
			struct pset *p;
			struct clause *n;

			p = pset_remove(c->literals, -name);
			/* c is unsatisfiable */
			if (p == NULL)
				return 0;

			n = c + 1;
			n->literals = p;
			n->mark = mark;
			n->sat = 0;
			cnf->clauses[l->clauses[i]] = n;
		}
	}

	return 1;
}

static struct literal *remove_zliteral(struct cnf *cnf, int v)
{
	struct literal *l;

	assert(!list_empty(&cnf->z));
	assert(v > 0);

	l = &cnf->lbuf[v-1];
	list_remove(&l->elt.dl);
	return l;
}

static int unit_propagate(struct cnf *cnf, unsigned mark)
{
	size_t i;
	int result = -1;

	for (i = 0; i < cnf->nclauses; i++) {
		struct clause *c = cnf->clauses[i];
		struct literal *l;
		int success;

		assert(c != NULL);
		/* if literals is NULL, then the clause is already unsat */
		assert(c->literals != NULL);

		if (c->sat || c->literals->cnt != 1)
			continue;

		if (c->literals->val < 0)
			l = &cnf->lbuf[-c->literals->val - 1];
		else
			l = &cnf->lbuf[c->literals->val - 1];
		success = try_set(cnf, mark, l, c->literals->val);
		if (!success)
			return 0;

		result = 1;
		if (c->literals->val < 0) {
			struct literal *f;

			f = remove_zliteral(cnf, -c->literals->val);

			assert(f != NULL);
			assert(f->name == -c->literals->val);

			f->mark = mark;
			f->elt.next = cnf->f;
			cnf->f = f;
		} else {
			struct literal *t;

			t = remove_zliteral(cnf, c->literals->val);

			assert(t != NULL);
			assert(t->name == c->literals->val);

			t->mark = mark;
			t->elt.next = cnf->t;
			cnf->t = t;
		}
	}

	return result;
}

static int is_pure_literal(struct cnf *cnf, struct literal *l, int val)
{
	size_t i;

	for (i = 0; i < l->nclauses; i++) {
		size_t c = l->clauses[i];
		assert(cnf->clauses[c] != NULL);
		if (cnf->clauses[c]->sat)
			continue;

		if (pset_contains(cnf->clauses[c]->literals, -val))
			return 0;
	}

	return 1;
}

static int eliminate_pure_literals(struct cnf *cnf, unsigned mark)
{
	struct dl *next;
	struct dl *i;
	int result = -1;

	for (i = list_start(&cnf->z); i != list_end(&cnf->z); i = next) {
		struct literal *l = containerof(i, struct literal, elt);

		next = i->next;

		if (is_pure_literal(cnf, l, l->name)) {
			if (!try_set(cnf, mark, l, l->name))
				return 0;

			list_remove(&l->elt.dl);
			l->mark = mark;
			l->elt.next = cnf->t;
			cnf->t = l;

			result = 1;
		} else if (is_pure_literal(cnf, l, -l->name)) {
			if (!try_set(cnf, mark, l, l->name))
				return 0;

			list_remove(&l->elt.dl);
			l->mark = mark;
			l->elt.next = cnf->f;
			cnf->f = l;

			result = 1;
		}
	}

	return result;
}

static int sat(struct cnf *cnf, unsigned mark)
{
	struct literal *l;
	int rc;

	if (satisfied(cnf))
		return 1;
	else if (list_empty(&cnf->z))
		return 0;

	rc = unit_propagate(cnf, mark);
	if (rc == 1)
		return sat(cnf, mark + 1);
	else if (rc == 0)
		return 0;

	rc = eliminate_pure_literals(cnf, mark);
	if (rc == 1)
		return sat(cnf, mark + 1);
	else if (rc == 0)
		return 0;

	/* can't unit-propagate or eliminate pure literals---have to guess */
	assert(!list_empty(&cnf->z));
	l = containerof(list_start(&cnf->z), struct literal, elt);
	list_remove(&l->elt.dl);
	l->mark = mark;
	assert(l->name > 0);

	/* first, try setting to 'true' */
	l->elt.next = cnf->t;
	cnf->t = l;

	if (try_set(cnf, mark, l, l->name)) {
		if (sat(cnf, mark + 1))
			return 1;
	}
	unwind(cnf, mark);
	list_remove(&l->elt.dl);

	/* next, try setting to 'false' */
	l->mark = mark;
	l->elt.next = cnf->f;
	cnf->f = l;

	if (try_set(cnf, mark, l, -l->name)) {
		if (sat(cnf, mark + 1))
			return 1;
	}

	return 0;
}

static struct cnf *dimacs_header(FILE *f)
{
	/*
	 * TODO: this is pretty hacky, should probably generate a parser with
	 * ragel or something
	 */
	struct cnf *result;
	unsigned nvars, nclauses;
	int rc;

	/* parse out comment lines */
	for (;;) {
		int c;
		c = fgetc(f);
		if (c == 'c') {
			while (fgetc(f) != '\n')
				;
		} else {
			ungetc(c, f);
			break;
		}
	}

	rc = fscanf(f, " p cnf %u %u ", &nvars, &nclauses);
	if (rc != 2)
		errx(EXIT_FAILURE, "failed parsing dimacs header");

	result = calloc(1, sizeof(*result) + nclauses * sizeof(struct clause *));
	if (result == NULL)
		err(EXIT_FAILURE, "malloc: cnf: %u %u", nvars, nclauses);

	result->nvars = nvars;
	result->nclauses = nclauses;
	list_init(&result->z);

	return result;
}

static void append_clause(struct literal *l, size_t c)
{
	size_t *clauses;

	clauses = realloc(l->clauses, (l->nclauses + 1) * sizeof(size_t));
	if (clauses == NULL)
		err(EXIT_FAILURE, "realloc: clauses");
	l->clauses = clauses;
	l->clauses[l->nclauses] = c;
	l->nclauses++;
}

static struct clause *dimacs_clause(FILE *f, struct cnf *cnf, size_t c)
{
	struct clause *result;
	struct clause *expanded;

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
			append_clause(&cnf->lbuf[-literal - 1], c);
		else
			append_clause(&cnf->lbuf[literal - 1], c);
	}

	expanded = realloc(result,
			   sizeof(*expanded)*(result->literals->cnt + 1));
	if (expanded == NULL)
		err(EXIT_FAILURE, "realloc: clause");

	return expanded;
}

static struct cnf *dimacs(FILE *f)
{
	struct cnf *result;
	size_t i;

	result = dimacs_header(f);

	result->lbuf = calloc(result->nvars, sizeof(*result->lbuf));
	if (result->lbuf == NULL)
		err(EXIT_FAILURE, "calloc: lbuf");

	for (i = 0; i < result->nvars; i++) {
		struct literal *l = result->lbuf + i;
		l->mark = 0;
		l->name = i + 1;
		list_insert(&result->z, &l->elt.dl);
	}

	for (i = 0; i < result->nclauses; i++)
		result->clauses[i] = dimacs_clause(f, result, i);

	return result;
}

static void print_list(const struct literal *l, int polarity)
{
	const struct literal *i;

	for (i = l; i != NULL; i = i->elt.next)
		printf("  %d\n", polarity * i->name);
}

static void usage(const char *prog)
{
	fprintf(stderr, "usage: %s [cnf file]\n", prog);
}

static void handle(int sig)
{
	UNUSED(sig);
	exit(EXIT_FAILURE);
}

int main(int argc, const char * const argv[])
{
	struct sigaction sa;
	struct cnf *cnf;
	FILE *in;
	size_t i;
	int issat;
	int rc;

	sa.sa_handler = handle;
	sigemptyset(&sa.sa_mask);
	sa.sa_flags = 0;
	sigaction(SIGINT, &sa, NULL);

	if (argc == 1) {
		in = stdin;
	} else if (argc == 2) {
		in = fopen(argv[1], "r");
		if (in == NULL)
			err(EXIT_FAILURE, "fopen: %s", argv[1]);
	} else {
		usage(argv[0]);
		return EXIT_FAILURE;
	}

	cnf = dimacs(in);

	if (argc == 2)
		fclose(in);

	issat = sat(cnf, 1);
	if (issat) {
		if (cnf->t != NULL)
			print_list(cnf->t, 1);
		if (cnf->f != NULL)
			print_list(cnf->f, -1);
		rc = EXIT_SUCCESS;
	} else {
		assert(cnf->f == NULL);
		assert(cnf->t == NULL);
		rc = EXIT_FAILURE;
	}

	unwind_all(cnf);

	for (i = 0; i < cnf->nvars; i++)
		free(cnf->lbuf[i].clauses);
	free(cnf->lbuf);
	free(cnf);

	return rc;
}
