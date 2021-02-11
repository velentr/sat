#!/usr/bin/env julia

struct Literal
    name
    polarity
end
function Literal(v)
    if v < 0
        Literal(-v, false)
    else
        Literal(v, true)
    end
end

struct Cnf
    clauses
end

function firstclause(dimacs)
    line = readline(dimacs)
    while startswith(line, 'c') || startswith(line, 'p')
        line = readline(dimacs)
    end

    return line
end

function Cnf(f::String)
    clauses = []
    dimacs = open(f, "r")
    line = firstclause(dimacs)
    push!(clauses, Set())
    while line != ""
        literals = [parse(Int, l) for l in split(line)]
        i = 1
        while (i = findnext(l -> l == 0, literals, i)) != nothing
            union!(clauses[1], map(Literal, literals[1:i-1]))
            pushfirst!(clauses, Set())
            literals = literals[i+1:length(literals)]
        end
        union!(clauses[1], map(Literal, literals))

        line = readline(dimacs)
    end

    @assert isempty(clauses[1]) "dimacs not terminated with 0"
    popfirst!(clauses)

    Cnf(reverse(clauses))
end

function check(assignments, cnf)
    assigned = Set()
    # Note that unsat is a set instead of an array here. This will
    # work since if two clauses are identical, they will both be
    # satisfied by the same conditions.
    unsat = Set(cnf.clauses)

    for v in assignments
        l = Literal(v)
        @assert !(l.name in assigned) "literal is already assigned"
        union!(assigned, [l.name])

        for clause in unsat
            if l in clause
                setdiff!(unsat, [clause])
            end
        end
    end

    @assert isempty(unsat) "not all clauses are satisfied"
end

assignments = [parse(Int, line) for line in readlines(stdin)]
cnf = Cnf(ARGS[1])
check(assignments, cnf)
