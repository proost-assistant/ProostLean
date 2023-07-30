# -*- coding: utf-8 -*

import os

dir_path = os.path.dirname(os.path.realpath(__file__))

add_def = "def add := fun x: Nat => Nat_rec.{1} (fun a : Nat => Nat) x (fun a n: Nat => Succ n)\n\n" 

def unary(n) :
    res = "Zero"
    for i in range(n):
        res = f"Succ ({res})"
    return res

def def_n(n) :
    return f"def n{str(n)} := {unary(n)}\n\n"

def preuve_eq_double_n(n) :
    return f"def p{str(n)} : Eq.{{1}} Nat n{str(2*n)} (add n{str(n)} n{str(n)}) := Refl.{{1}} Nat n{str(2*n)}\n\n"

def make_file_at_root(n, root) :
    file = f"{root}/test_{str(n)}.mdln"
    f = open(file, "w")
    f.write(add_def)
    f.write(def_n(n))
    f.write(def_n(2*n))
    f.write(preuve_eq_double_n(n))
    f.close() 

def make_file(n) :
    make_file_at_root(n,dir_path)