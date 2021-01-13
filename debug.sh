#!/bin/sh

gcc sat.c pset.c -O0 -g -std=c99 -pedantic -Wall -Wextra -Werror -o sat.debug
gcc pset_test.c pset.c -O0 -g -std=c99 -pedantic -Wall -Wextra -Werror -o pset.test
