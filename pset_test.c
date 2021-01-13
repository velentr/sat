#include <assert.h>
#include <stdlib.h>
#include <stdio.h>

#include "pset.h"

static void check_pset(int val, void *_user)
{
	int *user = _user;

	assert(val == *user);
	(*user)++;
}

static void check_odd_pset(int val, void *_user)
{
	int *user = _user;

	assert(val == *user);
	*user += 2;
}

int main()
{
	struct pset *pset = NULL;
	struct pset *odd;
	int val;
	int i;

	pset = pset_insert(pset, 5);
	pset = pset_insert(pset, 8);
	pset = pset_insert(pset, 6);
	pset = pset_insert(pset, 7);
	pset = pset_insert(pset, 2);
	pset = pset_insert(pset, 3);
	pset = pset_insert(pset, 1);
	pset = pset_insert(pset, 4);

	val = 1;
	pset_foreach(pset, check_pset, &val);
	assert(pset->cnt == 8);
	assert(pset_contains(pset, 7));
	assert(!pset_contains(pset, 10));

	odd = pset;
	pset_refup(odd);
	for (i = 2; i < 9; i += 2) {
		struct pset *tmp;

		tmp = pset_remove(odd, i);
		pset_refdown(odd);
		odd = tmp;
	}

	val = 1;
	pset_foreach(pset, check_pset, &val);
	assert(pset->cnt == 8);

	val = 1;
	pset_foreach(odd, check_odd_pset, &val);
	assert(odd->cnt == 4);
	assert(!pset_contains(odd, 4));

	pset_refdown(odd);
	pset_refdown(pset);

	return EXIT_SUCCESS;
}
