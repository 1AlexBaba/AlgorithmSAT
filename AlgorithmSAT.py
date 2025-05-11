#!/usr/bin/env python3
"""
sat_experiment.py – resolution, DP, and DPLL variants with a tiny benchmark.
"""

import random
import time
import tracemalloc
import pandas as pd


# ───────────────────────────────────────────────────────── CNF helpers ──
def generate_random_3sat(n_vars: int, n_clauses: int, seed=None):
    rng = random.Random(seed)
    cnf = []
    for _ in range(n_clauses):
        clause = set()
        while len(clause) < 3:
            var = rng.randint(1, n_vars)
            lit = var if rng.choice([True, False]) else -var
            clause.add(lit)
        cnf.append(frozenset(clause))
    return cnf


# ───────────────────────────────────────────────────────── Resolution ──
def resolution(cnf):
    cnf = [set(cl) for cl in cnf]
    new = set()
    while True:
        pairs = []
        n = len(cnf)
        for i in range(n):
            for j in range(i + 1, n):
                if any(l in cnf[j] and -l in cnf[i] for l in cnf[i]):
                    pairs.append((cnf[i], cnf[j]))

        for Ci, Cj in pairs:
            for lit in Ci:
                if -lit in Cj:
                    resolv = (Ci - {lit}) | (Cj - {-lit})
                    if any(l in resolv and -l in resolv for l in resolv):
                        continue
                    if not resolv:
                        return False        # empty clause → UNSAT
                    new.add(frozenset(resolv))

        new_clauses = [cl for cl in new if cl not in cnf]
        if not new_clauses:
            return True                     # no progress → SAT
        cnf.extend(new_clauses)


# ───────────────────────────────────────────────────────── Davis-Putnam ──
def dp(cnf, heuristic='naive', seed=None):
    rng = random.Random(seed)
    cnf = [set(cl) for cl in cnf]
    while True:
        if not cnf:
            return True                     # all clauses satisfied
        if any(len(cl) == 0 for cl in cnf):
            return False                    # empty clause → UNSAT

        vars_ = {abs(l) for cl in cnf for l in cl}
        var = rng.choice(list(vars_)) if heuristic == 'random' else next(iter(vars_))

        pos = [cl for cl in cnf if var in cl]
        neg = [cl for cl in cnf if -var in cl]
        resolvents = []
        for C in pos:
            for D in neg:
                r = (C | D) - {var, -var}
                if any(l in r and -l in r for l in r):
                    continue
                resolvents.append(frozenset(r))

        cnf = [cl for cl in cnf if var not in cl and -var not in cl]
        cnf.extend(resolvents)
        cnf = [set(cl) for cl in set(map(frozenset, cnf))]


# ─────────────────────────────────── DPLL (with three branching rules) ──
def unit_propagate(cnf, assignment):
    changed = True
    cnf = list(cnf)
    while changed:
        changed = False
        for cl in [c for c in cnf if len(c) == 1]:
            lit = next(iter(cl))
            var, val = abs(lit), lit > 0
            if var in assignment:
                if assignment[var] != val:
                    return None, None       # conflict
                continue
            assignment[var] = val
            changed = True

        new_cnf = []
        for cl in cnf:
            if any((lit > 0 and assignment.get(abs(lit)) is True) or
                   (lit < 0 and assignment.get(abs(lit)) is False) for lit in cl):
                continue                    # clause satisfied
            new_clause = {l for l in cl if abs(l) not in assignment}
            if not new_clause:
                return None, None           # empty → conflict
            new_cnf.append(frozenset(new_clause))
        cnf = new_cnf
    return cnf, assignment


def pure_literal_assign(cnf, assignment):
    lits = {l for cl in cnf for l in cl}
    pures = {l for l in lits if -l not in lits}
    for lit in pures:
        assignment[abs(lit)] = lit > 0
    cnf = [cl for cl in cnf if all(abs(l) not in assignment for l in cl)]
    return cnf, assignment


def choose_var(cnf, assignment, heuristic='naive', rng=None):
    rng = rng or random
    unassigned = {abs(l) for cl in cnf for l in cl if abs(l) not in assignment}
    if not unassigned:
        return None
    if heuristic == 'random':
        return rng.choice(list(unassigned))
    if heuristic == 'dlis':
        counter = {}
        for cl in cnf:
            for lit in cl:
                if abs(lit) not in assignment:
                    counter[lit] = counter.get(lit, 0) + 1
        chosen = max(counter, key=counter.get)
        return abs(chosen)
    return next(iter(unassigned))           # naive


def dpll_rec(cnf, assignment, heuristic='naive', rng=None):
    cnf, assignment = unit_propagate(cnf, assignment)
    if cnf is None:
        return False, None
    if not cnf:
        return True, assignment

    cnf, assignment = pure_literal_assign(cnf, assignment)
    if not cnf:
        return True, assignment

    var = choose_var(cnf, assignment, heuristic, rng)
    for value in (True, False):
        new_assign = assignment | {var: value}
        new_cnf = [frozenset({l for l in cl if abs(l) != var})
                   for cl in cnf
                   if not ((value and var in cl) or (not value and -var in cl))]
        if any(len(cl) == 0 for cl in new_cnf):
            continue
        sat, model = dpll_rec(new_cnf, new_assign, heuristic, rng)
        if sat:
            return True, model
    return False, None


def dpll(cnf, heuristic='naive', seed=None):
    rng = random.Random(seed)
    return dpll_rec(cnf, {}, heuristic, rng)


# ───────────────────────────────────────────────────────── Experiment ──
def run_experiment():
    results = []
    algos = ['resolution', 'dp', 'dpll_naive', 'dpll_random', 'dpll_dlis']

    for n, m in [(8, 30), (10, 40), (12, 50)]:
        for sample in range(2):
            cnf = generate_random_3sat(n, m, seed=100 * n + sample)
            for algo in algos:
                tracemalloc.start()
                start = time.perf_counter()

                if algo == 'resolution':
                    sat = resolution(cnf)
                elif algo == 'dp':
                    sat = dp(cnf)
                elif algo == 'dpll_naive':
                    sat, _ = dpll(cnf, 'naive', seed=sample)
                elif algo == 'dpll_random':
                    sat, _ = dpll(cnf, 'random', seed=sample)
                else:
                    sat, _ = dpll(cnf, 'dlis', seed=sample)

                elapsed = time.perf_counter() - start
                _, peak = tracemalloc.get_traced_memory()
                tracemalloc.stop()

                results.append(dict(
                    n_vars=n, n_clauses=m, sample=sample,
                    algorithm=algo, satisfiable=sat,
                    time_sec=elapsed, peak_memory_kb=peak / 1024
                ))

    return pd.DataFrame(results)


# ──────────────────────────────────────────────────────────── main() ──
def main(show_tables=True):
    df = run_experiment()
    summary = (df.groupby('algorithm')
                 .agg(time_sec=('time_sec', 'mean'),
                      peak_memory_kb=('peak_memory_kb', 'mean'))
                 .reset_index())

    if show_tables:
        try:
            import ace_tools as tools
            tools.display_dataframe_to_user('SAT Experiment Raw', df)
            tools.display_dataframe_to_user('SAT Experiment Summary', summary)
        except ModuleNotFoundError:
            print("⚠  ace_tools not found – falling back to console output.\n")
            print("── Raw results ──")
            print(df.to_string(index=False))
            print("\n── Summary (mean over all runs) ──")
            print(summary.to_string(index=False))
    return df, summary


if __name__ == "__main__":
    main()
