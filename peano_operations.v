Check mult_n_O.

Check mult_n_Sm.

Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity.
Qed.

Theorem mult_n_1 : forall p : nat,
  p * 1 = p.
Proof.
  intros.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity.
Qed.

Theorem addition_commutative : forall p q : nat,
  p + q = q + p.
Proof.
  induction p.
    simpl.
    induction q.
      reflexivity.
      simpl.
      rewrite <- IHq.
      reflexivity.
    induction q.
      simpl.
      rewrite IHp. simpl. reflexivity.
      simpl. rewrite <- IHq.
      simpl. rewrite IHp.
      simpl. rewrite IHp. reflexivity.
Qed.

Theorem multiplication_commutative : forall p q : nat,
  p * q = q * p.
Proof.
  intros.
  induction p.
    simpl.
    induction q.
      reflexivity.
      simpl.
      apply IHq.
    simpl.
    rewrite <- mult_n_Sm.
    rewrite <- IHp.
    apply addition_commutative.
Qed.

Theorem addition_associative : forall m n o : nat,
  (m + n) + o = m + (n + o).
Proof.
  intros.
  induction m.
    simpl. reflexivity.
    simpl. rewrite <- IHm. reflexivity.
Qed.

Theorem conv : forall m n : nat,
  m * S n = m + m * n.
Proof.
  intros. induction m.
    simpl. reflexivity.
    simpl. rewrite IHm. rewrite <- addition_associative. rewrite (addition_commutative (n)).
    rewrite addition_associative. reflexivity.
Qed.

Theorem right_distributive : forall a b c : nat,
  (a+b)*c=(a*c)+(b*c).
Proof.
  intros.
  induction c.
    rewrite multiplication_commutative. simpl. rewrite mult_n_0_m_0. reflexivity.
    rewrite multiplication_commutative. simpl.
    rewrite <- multiplication_commutative. rewrite IHc. rewrite <- addition_associative.
    rewrite (addition_commutative (a+b)). rewrite <- addition_associative. rewrite (addition_commutative (a*c)).
    rewrite addition_associative. rewrite conv. rewrite conv. reflexivity.
Qed.

Theorem multiplication_associative : forall m n o : nat,
  (m*n)*o=m*(n*o).
Proof.
  intros.
  induction m.
    simpl. reflexivity.
    simpl. rewrite <- IHm.
    apply right_distributive. 
Qed.

Theorem left_distributive : forall a b c : nat,
  a*(b+c)=(a*b)+(a*c).
Proof.
  intros. rewrite multiplication_commutative. rewrite right_distributive.
  rewrite multiplication_commutative. rewrite addition_commutative. rewrite multiplication_commutative.
  rewrite addition_commutative. reflexivity.
Qed.