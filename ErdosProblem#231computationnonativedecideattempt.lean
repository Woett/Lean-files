import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
We define the four-letter alphabet Alphabet = {a, b, c, d} and the cyclic permutation sigma. We then define Keränen's morphism g. g(a) is given explicitly, and g(b), g(c), g(d) are obtained by applying sigma cyclically.
-/
inductive Alphabet
| a | b | c | d
deriving DecidableEq

open Alphabet

def sigma_perm : Alphabet → Alphabet
| a => b
| b => c
| c => d
| d => a

def charToAlphabet (char : Char) : Alphabet :=
  match char with
  | 'a' => a
  | 'b' => b
  | 'c' => c
  | 'd' => d
  | _ => a

def stringToAlphabet (s : String) : List Alphabet :=
  s.toList.map charToAlphabet

def g_a_str := "abcacdcbcdcadcdbdabacabadbabcbdbcbacbcdcacbabdabacadcbcdcacdbcbacbcdcacdcbdcdadbdcbca"

def g_a : List Alphabet := stringToAlphabet g_a_str

def g : Alphabet → List Alphabet
| a => g_a
| b => g_a.map sigma_perm
| c => g_a.map (sigma_perm ∘ sigma_perm)
| d => g_a.map (sigma_perm ∘ sigma_perm ∘ sigma_perm)

/-
Optimized computational verification functions.
-/
def count_v2 (l : List Alphabet) (x : Alphabet) : Nat :=
  l.foldl (fun n y => if x == y then n + 1 else n) 0

def isPerm_v2 (u v : List Alphabet) : Bool :=
  count_v2 u a == count_v2 v a &&
  count_v2 u b == count_v2 v b &&
  count_v2 u c == count_v2 v c &&
  count_v2 u d == count_v2 v d

def isSquareFreeSuffixBoundary (w : List Alphabet) (added_len : Nat) : Bool :=
  let min_k := added_len / 2 + 1
  let max_k := w.length / 2
  if min_k > max_k then true
  else
    (List.range (max_k - min_k + 1)).all (fun i =>
      let k := min_k + i
      let u := (w.drop (w.length - 2 * k)).take k
      let v := w.drop (w.length - k)
      not (isPerm_v2 u v))

def check_prefixes_g_optimized (current_g : List Alphabet) (next_g : List Alphabet) : Bool :=
  (List.range next_g.length).all (fun i =>
    let p := next_g.take (i + 1)
    isSquareFreeSuffixBoundary (current_g ++ p) p.length)

def dfs_check_optimized (w : List Alphabet) (g_w : List Alphabet) (depth : Nat) : Bool :=
  match depth with
  | 0 => true
  | depth + 1 =>
    [a, b, c, d].all (fun x =>
      let w_next := w ++ [x]
      if isSquareFreeSuffixBoundary w_next 1 then
        let gx := g x
        if check_prefixes_g_optimized g_w gx then
          dfs_check_optimized w_next (g_w ++ gx) depth
        else false
      else true)
termination_by depth
decreasing_by all_goals (simp_wf; try omega)

/-
Checking equation lemmas and evaluating the function.
-/
#check dfs_check_optimized.eq_def
#eval dfs_check_optimized [] [] 4

/-
Defining a structurally recursive version of the verification function to enable kernel reduction, proving its equivalence to the original function, and proving the main result by computation.
-/
def dfs_check_computable (w : List Alphabet) (g_w : List Alphabet) (depth : Nat) : Bool :=
  match depth with
  | 0 => true
  | n + 1 =>
    [a, b, c, d].all (fun x =>
      let w_next := w ++ [x]
      if isSquareFreeSuffixBoundary w_next 1 then
        let gx := g x
        if check_prefixes_g_optimized g_w gx then
          dfs_check_computable w_next (g_w ++ gx) n
        else false
      else true)

theorem dfs_check_optimized_eq_computable (w : List Alphabet) (g_w : List Alphabet) (depth : Nat) :
  dfs_check_optimized w g_w depth = dfs_check_computable w g_w depth := by
    convert dfs_check_optimized.eq_def w g_w depth using 1;
    convert dfs_check_computable.eq_def w g_w depth using 1;
    field_simp;
    congr! 2;
    congr! 2;
    congr! 3;
    funext w g_w depth; exact (by
    induction' depth with depth ih generalizing w g_w;
    · -- By definition of `dfs_check_optimized` and `dfs_check_computable`, we can see that they are equivalent for `depth = 0`.
      simp [dfs_check_optimized, dfs_check_computable];
    · unfold dfs_check_optimized dfs_check_computable; aesop;)

#print axioms dfs_check_optimized_eq_computable