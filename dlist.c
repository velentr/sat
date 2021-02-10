#include <stdlib.h>

struct dl {
	struct dl *prev;
	struct dl *next;
};

struct list {
	struct dl canary;
};

static void list_init(struct list *l)
{
	l->canary.next = &l->canary;
	l->canary.prev = &l->canary;
}

static void list_insert(struct list *l, struct dl *elt)
{
	elt->next = l->canary.next;
	elt->prev = &l->canary;
	l->canary.next->prev = elt;
	l->canary.next = elt;
}

static void list_remove(struct dl *elt)
{
	elt->prev->next = elt->next;
	elt->next->prev = elt->prev;
#if !defined(NDEBUG)
	elt->next = NULL;
	elt->prev = NULL;
#endif
}

static int list_empty(struct list *l)
{
	return l->canary.next == &l->canary;
}

static struct dl *list_start(struct list *l)
{
	return l->canary.next;
}

static struct dl *list_end(struct list *l)
{
	return &l->canary;
}
