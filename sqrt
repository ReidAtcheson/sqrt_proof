Require Import QArith.QArith_base.
Require Import QArith.Qabs.
Require Import Psatz.
Require Import Init.Nat.




(*Iterative algorithm that computes n successive approximations
  to the square root of the input c using an initial guess x0. *)
Fixpoint sqrt (c:Q) (x0:Q) (n:nat) := 
  match n with
  | O => x0
  | S p => (sqrt c (x0*(1#2) + (c/x0)*(1#2)) p)
  end.


(*Simple sanity check that we are doing the right iteration.*)
Definition twoQ:Q := 2#1.
Eval compute in (sqrt twoQ 1 5).

(*We can't compute the actual error of the sqrt algorithm (that would
  require knowing the actual square root of the input number, which we are
  using the algorithm itself to compute) - I define an error-like function
  which tells us how close the sqrt function output is to satisfying
  (sqrt c x0 n) * (sqrt c x0 n) - c = 0
  The goal then is to prove that as we increase the number of successive 
  approximations (the parameter "n" in sqrt), the sqrt_err function decreases
  to 0. Since this is a constructive argument, we actually have to provide
  a function that computes "n" given a desired input error.
*)
Definition sqrt_err (c:Q) (x0:Q) (n:nat) := (sqrt c x0 n)*(sqrt c x0 n) - c.

(*One key property of sqrt_err is that if c>=0, then no matter 
  what x0 we pick as an initial guess,
  we will always have (sqrt_err c x0 1)>=0.*)

Theorem sqrt_err_poscondition : forall c x0, c>=0 -> sqrt_err c x0 1 >= 0.
Proof.
Admitted.

