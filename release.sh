#!/bin/sh

gcc sat.c -O3 -march=native -std=c99 -pedantic -Wall -DNDEBUG -o sat.release
