#ifndef PSET_H_
#define PSET_H_


struct pset {
	struct pset *left;
	struct pset *right;
	int val;
	unsigned cnt;
	unsigned ref;
};

struct pset *pset_insert(struct pset *pset, int val);
struct pset *pset_remove(struct pset *pset, int val);
int pset_contains(const struct pset *pset, int val);

void pset_refup(struct pset *pset);
void pset_refdown(struct pset *pset);

void pset_foreach(struct pset *pset, void (*iter)(int, void *),
		  void *user);


#endif /* PSET_H_ */
