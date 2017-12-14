Require Import QArith.QArith_base.
Require Import QArith.Qabs.
Require Import Psatz.
Require Import Init.Nat.
Require Import Omega.




(*Iterative algorithm that computes n successive approximations
  to the square root of the input c using an initial guess x0. *)
Fixpoint sqrt_fast (c:Q) (x0:Q) (n:nat) := 
  match n with
  | O => x0
  | S p => (sqrt_fast c (x0*(1#2) + (c/x0)*(1#2)) p)
  end.

Fixpoint sqrt (c:Q) (x0:Q) (n:nat) :=
  match n with
  | O => x0
  | S p => (1#2)*(sqrt c x0 p) + (1#2)*(c/(sqrt c x0 p))
  end.

(*Simple sanity check that we are doing the right iteration.*)
Definition twoQ:Q := 2#1.
Eval compute in (sqrt twoQ 1 5).

Eval compute in ( (sqrt twoQ 1 4)*(1#2) + (1#2)*(twoQ/(sqrt twoQ 1 4))).

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

(*One key property of sqrt_err is that if c>=0 and n>=1, then no matter 
  what x0 we pick as an initial guess,
  we will always have (sqrt_err c x0 n)>=0.*)


Lemma r_squared_nonneg : forall (r:Q), r*r>=0.
Proof.
intros.
nra.
Qed.


Theorem sqrt_formula : forall c x0 n, c>=0 /\ (n>=1)%nat /\ x0>0 -> sqrt c x0 n == (1#2)*(sqrt c x0 (n-1))+(1#2)*(c/(sqrt c x0 (n-1))).
Proof.
intros.
destruct n.
* assert( (0>=1)%nat ). apply H. assert( not (0>=1)%nat ). auto with *. eauto with *.
* simpl. assert( (n-0)%nat = n). auto with *. rewrite H0. lra.
Qed.


Lemma nonneg_div_pos_isnonneg : forall a b, a>=0/\b>0 -> a/b>=0.
Proof.
intros.
destruct b.
{
  destruct Qnum.
  {
    assert( not (0<0#Qden) ).
    auto with *.
    assert( 0<0#Qden ). apply H.
    eauto with *.
  }
  {
    destruct a.
    destruct Qnum.
    {
      unfold Qdiv.
      assert( 0# Qden0 == 0).
      auto with *.
      rewrite H0.
      lra.
    }
    {
      unfold Qle.
      unfold Qdiv.
      unfold Qmult.
      simpl.
      auto with *.
    }
    {
      unfold Qle.
      unfold Qdiv. unfold Qmult.
      simpl.
      assert( not (0 <= Z.neg p0 # Qden0) ).
      {
        auto.
      }
      assert( (0 <= Z.neg p0 # Qden0) ). apply H.
      eauto with *.
    }
    
  }
  {
    assert( 0 < Z.neg p # Qden ). apply H.
    assert(not (0 < Z.neg p # Qden) ).
    {
      unfold Qlt.
      simpl.
      unfold Zlt.
      auto with *.
    }
    eauto with *.
  }
}
Qed.
Lemma sqrt_ispos : forall c x0 n, c>=0 /\ x0>0 -> (sqrt c x0 n > 0).
Proof.
intros.
induction n.
  {
    simpl.
    lra.
  }
  {
    simpl.
    remember (sqrt c x0 n) as m.
    assert( (c/m)>=0 ). apply nonneg_div_pos_isnonneg. lra.
    lra.
  }
Qed.

Theorem sqrt_err_poscondition : forall c x0 n, c>=0 /\ (n>=1)%nat /\ x0>0 -> sqrt_err c x0 n >= 0.
Proof.
intros.
unfold sqrt_err.
destruct n.
{
  eauto with *.
}
{
  simpl.
  assert(((1 # 2) * sqrt c x0 n +
 (1 # 2) * (c / sqrt c x0 n)) *
((1 # 2) * sqrt c x0 n +
 (1 # 2) * (c / sqrt c x0 n)) - c == ((1#2)*((sqrt c x0 n) - c/(sqrt c x0 n)))*((1#2)*((sqrt c x0 n) - c/(sqrt c x0 n)))).
  field.
  induction n.
  {
    simpl.
    assert( 
      (x0 * (1 # 2) + c / x0 * (1 # 2)) *
       (x0 * (1 # 2) + c / x0 * (1 # 2)) - c == ((1#2)*(x0 - c/x0))*((1#2)*(x0 - c/x0))
     ).
     {
      field.
      assert( 0 < x0). apply H.
      auto with *.
     }
     assert( 0<x0 ). apply H.
     lra.
  }
  {
    assert( sqrt c x0 (S n) > 0 ).
    {
      apply sqrt_ispos.
      lra.
    }
    lra.
  }
     rewrite H0.
     remember ((1 # 2) * (sqrt c x0 n - c / sqrt c x0 n)) as m.
     nra.
}
Qed.

(*The next key property of sqrt_err is that if c>=0, then regardless of
  what x0 we pick and if n>1, then (sqrt_err c x0 (n+1)) <= (sqrt_err c x0 n)/4.*)

Lemma a_leq_b_inva_geq_invb : forall a b, a>0 -> b>0 -> a>b -> /a < /b.
Proof.
intros.
unfold Qinv.
remember (Qnum a) as z1.
remember (Qnum b) as z2.
destruct z1. destruct z2.
* assert(not (0<a)). 
  assert( a == (Qnum a)#(Qden a) ). auto with *. 
  assert( (Qnum a) = 0%Z ). auto with *.
  rewrite H2.
  assert( a==0 ). auto with *.
  auto with *.
  eauto with *.
* auto with *.
* assert( not (0 < b) ).
  assert( b == (Qnum b)#(Qden b) ). auto with *.
  assert( (Qnum b) = Z.neg p). auto with *.
  rewrite H3 in H2.
  rewrite H2.
  unfold Qlt.
  simpl.
   
Qed.

Lemma big_den_makes_smaller : forall a b c, a>=0 -> b>0 -> c>0 -> b>c -> (a/b) <= (a/c).
intros.
destruct b.
destruct c.
assert(a / (Qnum # Qden) == Qden*a/QnumQed.

Theorem sqrt_err_decay : forall (c:Q) (x0:Q) (n:nat), (n>1)%nat /\ c>=0 /\ x0>0 -> 
(sqrt_err c x0 (S n)) <= (sqrt_err c x0 n)*(1#4).
Proof.
intros.
unfold sqrt_err.
simpl.
remember (sqrt c x0 n) as m.
assert( m>0 ). rewrite Heqm. apply (sqrt_ispos c x0 n). apply H.
assert( c/m >=0 ). apply nonneg_div_pos_isnonneg. lra.
assert(((1 # 2) * m + (1 # 2) * (c / m)) *
((1 # 2) * m + (1 # 2) * (c / m)) - c == (m*m + (c*c)/(m*m))*(1#4) - c/twoQ).
{
  unfold twoQ.
  field.
  lra.
}
rewrite H2.
unfold twoQ.
assert( m*m == c + sqrt_err c x0 n). unfold sqrt_err. rewrite Heqm. lra.
rewrite H3.
remember (sqrt_err c x0 n) as k.
assert(k>=0). rewrite Heqk. apply sqrt_err_poscondition.
assert( (n>=1)%nat ). auto with *.
assert( 0 <=c ). apply H.
assert( 0 < x0). apply H.
auto with *.
assert( ((c + k + c * c / (c + k)) * (1 # 4)) <= (c + k + c * c / (c )) * (1 # 4) ).
{
  assert( c+k >= c). lra.
  assert( (c*c)/(c+k) <= (c*c)/c ).
}
Qed.

(*The above theorems may be combined to give a bound on the convergence rate of
  sqrt_err*)
Theorem sqrt_err_convergence : forall (c:Q) (x0:Q) (n:nat), (n>1)%nat /\ c>=0 ->
(sqrt_err c x0 n) <= (sqrt_err c x0 1)*((1#4)^(Z_of_nat n)) /\ (sqrt_err c x0 n) >= 0.
Proof.
Admitted.


(*Finally we provide the function which gives us an "n" that will
guarantee a user-specified error criterion.*)

Theorem sqrt_with_specified_error (c:Q) (x0:Q) (err:Q) : c>=0 /\ x0>=0 /\ err>0 ->
{n:nat | sqrt_err c x0 n <= err}.
Proof.
Admitted.

