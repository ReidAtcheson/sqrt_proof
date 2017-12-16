Require Import QArith.QArith_base.
Require Import QArith.Qabs.
Require Import QArith.Qpower.
Require Import QArith.Qround.
Require Import ZArith.Znat.
Require Import Psatz.
Require Import Init.Nat.
Require Import Omega.





(*Iterative algorithm that computes n successive approximations
  to the square root of the input c using an initial guess x0. *)

(*This first version of sqrt_fast is considerably faster than the following
  definition, but this version is inconvenient for proofs.*)
Fixpoint sqrt_fast (c:Q) (x0:Q) (n:nat) := 
  match n with
  | O => x0
  | S p => (sqrt_fast c (x0*(1#2) + (c/x0)*(1#2)) p)
  end.

(*Easier to make proofs with this version of sqrt,*)
Fixpoint sqrt (c:Q) (x0:Q) (n:nat) :=
  match n with
  | O => x0
  | S p => (1#2)*(sqrt c x0 p) + (1#2)*(c/(sqrt c x0 p))
  end.

(*Should prove that answers are same, until then stuck computing with slow version.*)

(*Simple sanity check that we are doing the right iteration.*)
Definition twoQ:Q := 2#1.


Eval compute in ( (sqrt twoQ 1 4)*(1#2) + (1#2)*(twoQ/(sqrt twoQ 1 4))).
Eval compute in ( (sqrt_fast twoQ 1 5) ).

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

Lemma nonzero_r_squared_positive : forall (r:Q), r>0 -> r*r>0.
Proof.
intros.
nra.
Qed.


Theorem sqrt_formula : forall c x0 n, c>=0 /\ (n>=1)%nat /\ x0>0 -> sqrt c x0 n == (1#2)*(sqrt c x0 (n-1))+(1#2)*(c/(sqrt c x0 (n-1))).
Proof.
intros.
destruct n.
* assert(Hx: (0>=1)%nat ) by apply H.
  contradict Hx.
  auto with *.
* simpl.
  assert(Hx: (n-0)%nat = n) by auto with *.
  rewrite Hx.
  auto with *.
Qed.


Lemma nonneg_div_pos_isnonneg : forall a b, a>0/\b>0 -> a/b>0.
Proof.
intros.
destruct b.
destruct Qnum.
- assert( not (0<0#Qden) ) by auto with *.
  assert( 0<0#Qden ) by apply H.
  eauto with *.
- destruct a.
  destruct Qnum.
  + unfold Qdiv.
    assert( 0# Qden0 == 0) by auto with *.
    rewrite H0.
    lra.
  + unfold Qle, Qdiv, Qmult.
    simpl.
    auto with *.
  + unfold Qle, Qdiv, Qmult.
    simpl.
    assert( not (0 < Z.neg p0 # Qden0) ).
    {
      unfold Qlt.
      simpl.
      nia.
    }
    assert( (0 < Z.neg p0 # Qden0) ) by apply H.
    auto with *.
- assert(Hx: 0 < Z.neg p # Qden ) by apply H.
  (*assert(not (0 < Z.neg p # Qden) ).*)
  contradict Hx.
  unfold Qlt, Zlt.
  simpl.
  auto with *.
Qed.

Lemma sqrt_ispos : forall c x0 n, c>0 /\ x0>0 -> (sqrt c x0 n > 0).
Proof.
intros.
induction n; simpl.
- lra.
- remember (sqrt c x0 n) as m.
  assert( (c/m)>0 ). {
    apply nonneg_div_pos_isnonneg. lra.
  }
  lra.
Qed.

Theorem sqrt_err_poscondition : forall c x0 n, c>0 /\ (n>=1)%nat /\ x0>0 -> sqrt_err c x0 n >= 0.
Proof.
intros.
unfold sqrt_err.
destruct n.
- eauto with *.
- simpl.
  assert(Hx: ((1 # 2) * sqrt c x0 n +
 (1 # 2) * (c / sqrt c x0 n)) *
((1 # 2) * sqrt c x0 n +
 (1 # 2) * (c / sqrt c x0 n)) - c == ((1#2)*((sqrt c x0 n) - c/(sqrt c x0 n)))*((1#2)*((sqrt c x0 n) - c/(sqrt c x0 n)))). {
    field.
    induction n.
    - simpl.
      assert( 0<x0 ) by apply H.
      assert( 
        (x0 * (1 # 2) + c / x0 * (1 # 2)) *
         (x0 * (1 # 2) + c / x0 * (1 # 2)) - c == ((1#2)*(x0 - c/x0))*((1#2)*(x0 - c/x0))
       ).
       {
        field.
        auto with *.
       }
       lra.
    - assert( sqrt c x0 (S n) > 0 ). {
        apply sqrt_ispos.
        lra.
      }
      lra.
  }
  rewrite Hx.
  remember ((1 # 2) * (sqrt c x0 n - c / sqrt c x0 n)) as m.
  nra.
Qed.

(*The next key property of sqrt_err is that if c>=0, then regardless of
  what x0 we pick and if n>1, then (sqrt_err c x0 (n+1)) <= (sqrt_err c x0 n)/4.*)

Lemma num_inva_eq_dena : forall a, a > 0 -> (Qnum (/a) = Zpos (Qden a)).
Proof.
intros.
assert(Hy: a == (Qnum a)#(Qden a)) by auto with *.
unfold Qinv.
remember (Qnum a) as z1.
destruct z1.
* assert(Hx: (Qnum 0 = 0)%Z) by auto with *.
  rewrite Hy in H.
  assert(not (0 < 0 # Qden a)) by auto with *.
  contradiction.
* simpl. auto.
* rewrite Hy in *.
  assert(not (0 < (Z.neg p) # (Qden a) ) ). {
    unfold Qlt. simpl. nia.
  }
  contradiction.
Qed.

Lemma den_inva_eq_numa : forall a, a>0 -> ((Zpos (Qden (/a)))) = Qnum a.
Proof.
intros.
assert( a == (Qnum a) # (Qden a) ) by auto with *.
unfold Qinv.
remember (Qnum a) as z1.
destruct z1.
* rewrite H0 in H. assert( not (0 < 0#Qden a) ) by auto with *. contradiction.
* simpl. auto with *.
* rewrite H0 in H.
  assert(not (0< Z.neg p # Qden a)). {
    unfold Qlt. simpl. nia.
  }
  contradiction.
Qed.

Lemma a_leq_b_inva_geq_invb : forall a b, a>0 -> b>0 -> a>=b -> /a <= /b.
Proof.
intros.
unfold Qlt.
assert(Hx: Qnum (/a) = Zpos (Qden a) ) by auto using num_inva_eq_dena. (* auto applies H because it is in scope *)
assert(Hy: Qnum (/b) = Zpos (Qden b) ) by auto using num_inva_eq_dena.
unfold Qle.
rewrite Hx. rewrite Hy.
assert(Ha: ((Zpos (Qden (/b))) = Qnum b)%Z) by auto using den_inva_eq_numa.
assert(Hb: ((Zpos (Qden (/a))) = Qnum a)%Z) by auto using den_inva_eq_numa.
rewrite Ha. rewrite Hb. unfold Qle in H1.
nia.
Qed.

Lemma big_den_makes_smaller : forall a b c, a>0 -> b>0 -> c>0 -> b>=c -> (a/b) <= (a/c).
Proof.
intros.
unfold Qdiv.
assert( /b <= /c ) by auto using a_leq_b_inva_geq_invb.
assert(Ha: a* /b == /b * a) by lra.
assert(Hb: a * /c == /c * a) by lra.
rewrite Ha. rewrite Hb.
apply Qmult_le_compat_r; auto using a_leq_b_inva_geq_invb. (* auto applies the hypothesi in scope automatically *)
nra.
Qed.
Theorem sqrt_err_decay : forall (c:Q) (x0:Q) (n:nat), (n>=1)%nat /\ c>0 /\ x0>0 -> 
(sqrt_err c x0 (S n)) <= (sqrt_err c x0 n)*(1#4).
Proof.
intros.
unfold sqrt_err.
simpl.
remember (sqrt c x0 n) as m.
assert( m>0 ). {
  rewrite Heqm.
  apply (sqrt_ispos c x0 n).
  apply H.
}
assert( c/m >0 ) by (apply nonneg_div_pos_isnonneg; lra).
assert(Hx: ((1 # 2) * m + (1 # 2) * (c / m)) *
((1 # 2) * m + (1 # 2) * (c / m)) - c == (m*m + (c*c)/(m*m))*(1#4) - c/twoQ).
{
  unfold twoQ.
  field.
  lra.
}
rewrite Hx.
unfold twoQ.
assert(Hy: m*m == c + sqrt_err c x0 n). {
  unfold sqrt_err. rewrite Heqm. lra.
}
rewrite Hy.
remember (sqrt_err c x0 n) as k.
assert(k>=0). {
  rewrite Heqk.
  apply sqrt_err_poscondition.
  assert( (n>=1)%nat ) by auto with *.
  assert( 0 <c ) by apply H.
  assert( 0 < x0) by apply H.
  auto with *.
}
assert(R1: ((c + k + c * c / (c + k)) * (1 # 4) - c/(2#1) ) <= (c + k + c * c / (c )) * (1 # 4) - c/(2#1)).
{
  assert( c+k >= c) by lra.
  assert( (c*c)/(c+k) <= (c*c)/c ). {
    remember (c*c) as a. remember(c+k) as b.
    apply big_den_makes_smaller.
    rewrite Heqa.
    + assert(Hc: 0 < c) by lra.
      apply nonzero_r_squared_positive.
      apply Hc.
    + rewrite Heqb.
      lra.
    + lra.
    + lra.
  }
  lra.
}
assert(R2: c*c/c == c ). {
  assert(R: c*c/c == c*(c/c)) by (unfold Qdiv; lra).
  rewrite R; clear R.
  unfold Qdiv.
  assert(R: c * /c == 1) by (apply Qmult_inv_r; lra).
  rewrite R. lra.
}
rewrite R2 in *. (* when possible avoid naming where *)
assert(R3: (c + k + c) * (1 # 4) - c / (2 # 1) == (c+k-c)*(1#4)) by field.
rewrite R3 in *.
auto with *.
Qed.


Lemma nat_threecases : forall (n:nat), { (n=0)%nat } + {(n=1)%nat} + { (n>1)%nat}.
Proof.
intros.
induction n.
* auto with *.
* destruct IHn.
  - destruct s; auto with *. (* semi-colon makes applying auto to all branches. *)
  - auto.
Qed.

Lemma Qlt_hack : forall a b c, a>=0 -> b>=0 -> c>=0 -> a <= c -> a*b <= c*b.
Proof.
intros.
nra.
Qed.

Lemma Qpower_reduction : forall a (n:Z), (n>0)%Z -> a>0 -> a^n == a*(a^(n-1)).
Proof.
intros.
assert(R1: a== a^1) by lra.
remember (a^n) as an. remember ( a^(n-1)) as anm1.
rewrite R1; clear R1.
rewrite Heqan. rewrite Heqanm1.
remember ((n-1)%Z) as nm1.
assert(R: (n = 1 + (n-1))%Z) by auto with *.
rewrite R; clear R.
rewrite Heqnm1.
apply Qpower_plus.
lra.
Qed.

Lemma Zinject_to_nat_compat : forall (n:nat), (1<=n)%nat -> (Z.of_nat (n-1) = (Z.of_nat n) - 1)%Z.
Proof.
intros.
apply Nat2Z.inj_sub.
auto.
Qed.


(*The above theorems may be combined to give a bound on the convergence rate of
  sqrt_err*)
Theorem sqrt_err_convergence : forall (c:Q) (x0:Q) (n:nat), (n>1)%nat -> c>0 -> x0>0 ->
(sqrt_err c x0 n) <= (sqrt_err c x0 1)*((1#4)^(Z_of_nat (n-1))) /\ (sqrt_err c x0 n) >= 0.
Proof.
intros.
assert( 0 <= sqrt_err c x0 n). apply sqrt_err_poscondition. auto with *.
assert( sqrt_err c x0 n <= sqrt_err c x0 1 * (1 # 4) ^ Z.of_nat (n-1)).
{
  induction n.
  * assert( not (0>1)%nat ). auto with *. contradiction.
  * assert( sqrt_err c x0 (S n) <= (sqrt_err c x0 n)*(1#4) ). apply sqrt_err_decay.
  ** assert( {(n=0)%nat} + {(n=1)%nat} + { (n>1)%nat } ). apply nat_threecases.
     destruct H3. destruct s.
  + auto with *.
  + auto with *.
  + auto with *.
  ** assert( {(n=0)%nat} + {(n=1)%nat} + { (n>1)%nat } ). apply nat_threecases. destruct H4. destruct s.
  *** auto with *.
  *** rewrite e in H3. simpl. rewrite e. simpl. apply H3.
  *** assert(       sqrt_err c x0 n <=
      sqrt_err c x0 1 * (1 # 4) ^ Z.of_nat (n - 1) ).
      {
        apply IHn.
        apply g. apply sqrt_err_poscondition. auto with *.
      }
      assert( (S n - 1 = n)%nat ). auto with *. rewrite H5.
      assert( sqrt_err c x0 (S n) <=
sqrt_err c x0 1 * (1 # 4) ^ Z.of_nat (n-1)). nra.
      assert(
sqrt_err c x0 1 * (1 # 4) ^ Z.of_nat n == sqrt_err c x0 1 * (1#4) * (1 # 4) ^ Z.of_nat (n-1)).
{
  assert((1 # 4) ^ Z.of_nat n ==
    (1#4)* (1 # 4) ^ Z.of_nat (n - 1)).
  {
    remember (1#4) as a.
    remember (Z.of_nat n) as m.
    assert( (Z.of_nat (n-1) = m-1)%Z ).
    {
      rewrite Heqm.
      apply Nat2Z.inj_sub.
      auto with *.
    }
    rewrite H7.
    apply Qpower_reduction. auto with *. rewrite Heqa. lra.
  }
  rewrite H7.
  lra.
}
nra.
  
}
* auto with *.


Qed.


(*Finally we provide the function which gives us an "n" that will
guarantee a user-specified error criterion.*)




Definition normalize_error (err:Q) := 1 # (Qden err).

Lemma normalized_error_lt_error : forall err, err>0 -> normalize_error err <= err.
Proof.
intros.
unfold normalize_error.
unfold Qle.
simpl.
destruct err.
simpl.
assert((Qnum>=1)%Z).
{
  unfold Qlt in H. simpl in H. auto with *.
}
nia.
Qed.

Definition find_n (err:Q) := Zpos (Qden (normalize_error err)).
(*
Lemma Qpower_bound : forall (n:positive), Qpower_positive (1#4) n <= 1#n.
Proof.
intros.
induction n.
* assert( 1#n >= (1#(n~1)) ).
   {
      unfold Qle. simpl. nia.
   }
* simpl. unfold Qpower_positive. unfold Qinv. simpl. 
Qed.

Lemma find_n_works : forall err, err>0 -> (1#4)^(find_n err) <= err .
Proof.
intros.
unfold find_n.
unfold normalize_error.
simpl.
Qed.
*)
Fixpoint find_best_n (err:Q) (n:Z) (max:nat) := 
  if (Qlt_le_dec ((1#4)^n) err) then (n) else
  match max with
  |  O => (n+1)%Z
  |S p => find_best_n err (n+1) p
  end.



Definition sqrt_with_err (c:Q) (err:Q) := 
  let err1 := sqrt_err c c 1 in
  let err_final := err/err1 in
  let n := find_best_n err 0 (Z.to_nat (find_n err)) in
  sqrt c c (Z.to_nat n).
(*
  sqrt c c (Z.to_nat (find_n err_final)).

*)


Eval compute in (sqrt_with_err (2#1) (1#10)).
Eval compute in (sqrt_with_err (2#1) (1#100)).
Eval compute in (sqrt_with_err (2#1) (1#1000)).
Eval compute in (sqrt_with_err (2#1) (1#10000)).