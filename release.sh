#!/bin/sh

gcc sat.c pset.c -O2 -march=native -std=c99 -pedantic -Wall -DNDEBUG -o sat.release
