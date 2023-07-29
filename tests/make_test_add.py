# -*- coding: utf-8 -*

import os

add_def = "def add := fun x: Nat => Nat_rec.{1} (fun a : Nat => Nat) x (fun a n: Nat => succ n)\n\n" 

def unary(n) :
    res = "zero"
    for i in range(n):
        res = f"succ ({res})"
    return res

def def_n(n) :
    return f"def n{str(n)} := {unary(n)}\n\n"

def preuve_eq_double_n(n) :
    return f"def p{str(n)} : Eq.{{1}} Nat n{str(2*n)} (add n{str(n)} n{str(n)}) := refl.{{1}} Nat n{str(2*n)}\n\n"


def make_file(n, root) :
    file = f"{root}/test_{str(n)}.mdln"
    f = open(file, "w")
    f.write(add_def)
    f.write(def_n(n))
    f.write(def_n(2*n))
    f.write(preuve_eq_double_n(n))
    f.close() 

