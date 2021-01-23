#include <assert.h>
#include <err.h>
#include <stdlib.h>

#include "pset.h"

void pset_refup(struct pset *pset)
{
	if (pset != NULL) {
		assert(pset->ref > 0);
		pset->ref++;
	}
}

void pset_refdown(struct pset *pset)
{
	if (pset != NULL) {
		assert(pset->ref > 0);
		pset->ref--;
		if (pset->ref == 0) {
			pset_refdown(pset->left);
			pset_refdown(pset->right);
			free(pset);
		}
	}
}

static int pset_max(const struct pset *pset)
{
	assert(pset != NULL);

	if (pset->right == NULL)
		return pset->val;
	else
		return pset_max(pset->right);
}

static int pset_min(const struct pset *pset)
{
	assert(pset != NULL);

	if (pset->left == NULL)
		return pset->val;
	else
		return pset_min(pset->left);
}

static struct pset *pset_delete(struct pset *pset)
{
	struct pset *res;

	/* if there are no children, return an empty subtree */
	if (pset->left == NULL && pset->right == NULL)
		return NULL;

	/* if there is only one child, replace this node with the child */
	if (pset->left == NULL || pset->right == NULL) {
		struct pset *child;

		child = pset->left == NULL ? pset->right : pset->left;
		assert(child != NULL);
		pset_refup(child);

		return child;
	}

	assert(pset->left != NULL);
	assert(pset->right != NULL);

	res = malloc(sizeof(*res));
	if (res == NULL)
		err(EXIT_FAILURE, "malloc: pset");

	if (pset->right->cnt < pset->left->cnt) {
		unsigned val;

		val = pset_max(pset->left);
		res->left = pset_remove(pset->left, val);
		res->right = pset->right;
		pset_refup(res->right);
		res->cnt = pset->cnt - 1;
		res->ref = 1;
		res->val = val;

		assert(res->right != NULL);
		assert((res->left == NULL && res->cnt == res->right->cnt + 1)
		       || (res->cnt == res->left->cnt + res->right->cnt + 1));
	} else {
		unsigned val;

		val = pset_min(pset->right);
		res->right = pset_remove(pset->right, val);
		res->left = pset->left;
		pset_refup(res->left);
		res->cnt = pset->cnt - 1;
		res->ref = 1;
		res->val = val;

		assert(res->left != NULL);
		assert((res->right == NULL && res->cnt == res->left->cnt + 1)
		       || (res->cnt == res->left->cnt + res->right->cnt + 1));
	}

	return res;
}

struct pset *pset_remove(struct pset *pset, int val)
{
	struct pset *res;

	/* can't remove a value if it doesn't already exist */
	assert(pset != NULL);

	if (pset->val == val)
		return pset_delete(pset);

	res = malloc(sizeof(*res));
	if (res == NULL)
		err(EXIT_FAILURE, "malloc: pset");
	res->ref = 1;

	if (val < pset->val) {
		res->right = pset->right;
		pset_refup(res->right);

		res->left = pset_remove(pset->left, val);

		res->val = pset->val;
		res->cnt = pset->cnt - 1;
	} else {
		assert(pset->val < val);

		res->right = pset_remove(pset->right, val);

		res->left = pset->left;
		pset_refup(res->left);

		res->val = pset->val;
		res->cnt = pset->cnt - 1;
	}

	return res;
}

struct pset *pset_insert(struct pset *pset, int val)
{
	if (pset == NULL) {
		struct pset *res;

		res = malloc(sizeof(*res));
		if (res == NULL)
			err(EXIT_FAILURE, "malloc: pset");

		res->cnt = 1;
		res->ref = 1;
		res->val = val;
		res->left = NULL;
		res->right = NULL;

		return res;
	} else {
		assert(val != pset->val);

		pset->cnt++;

		if (val < pset->val) {
			pset->left = pset_insert(pset->left, val);
			return pset;
		} else {
			pset->right = pset_insert(pset->right, val);
			return pset;
		}
	}
}

int pset_contains(const struct pset *pset, int val)
{
	if (pset == NULL)
		return 0;

	if (pset->val == val)
		return 1;
	else if (pset->val < val)
		return pset_contains(pset->right, val);
	else
		return pset_contains(pset->left, val);
}

void pset_foreach(struct pset *pset, void (*iter)(int, void *),
		  void *user)
{
	if (pset != NULL) {
		pset_foreach(pset->left, iter, user);
		iter(pset->val, user);
		pset_foreach(pset->right, iter, user);
	}
}
