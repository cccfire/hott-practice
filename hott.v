From HoTT Require Import HoTT.

Section chapter_2.

Theorem path_reverse {A} (x y : A) :
  (x = y) -> (y = x).
intros.
path_induction.
reflexivity.
Qed.

Theorem path_concat {A} (x y z: A) :
  (x = y) -> (y = z) -> (x = z).
intros.
induction X0.
induction X.
reflexivity.
Qed.

(* 2.1.4 i *)

Theorem t_2_1_4_i {A} (x y : A) (p : x = y) :
  ((p = p @ (idpath y)) * (p = (idpath x) @ p)).
split.
all: induction p; reflexivity.
Qed.

Theorem t_2_1_4_ii {A} (x y : A) (p : x = y) :
  ((p^ @ p = (idpath y)) * (p @ p^ = (idpath x))).
split.
all: induction p; reflexivity.
Qed.

Theorem t_2_1_4_iii {A} (x y : A) (p : x = y) :
  (p^)^ = p.
induction p; reflexivity.
Qed.

Theorem t_2_1_4_iv {A} (x y z w : A) (p : x = y) (q : y = z) (r : z = w):
  p @ (q @ r) = (p @ q) @ r.
induction p.
induction q.
induction r.
reflexivity.
Qed.

Definition runit {A} {a b : A} (p : a = b) : p = p @ idpath b := match p with idpath => 1 end.
Definition lunit {A} {a b : A} (p : a = b) : p = idpath a @ p := match p with idpath => 1 end.


Definition rwhisker {A} {a b c : A} {p q : a = b} (alph : p = q) (r : b = c)
 : p @ r = q @ r := 
  match alph with idpath => 1 end.

Definition lwhisker {A} {a b c : A} (q : a = b) {r s : b = c} (bet : r = s)
 : q @ r = q @ s := 
  match bet with idpath => 1 end.

Theorem rwhisker_1 {A} {a b : A} (p q : a = b) (alph : p = q) :
  (rwhisker alph (idpath b)) = (runit p)^ @ alph @ (runit q).
Proof.
  induction p.
  induction alph.
  unfold rwhisker.
  unfold runit.
  cbn.
  reflexivity.
Qed.

Theorem lwhisker_1 {A} {b c : A} (r s : b = c) (bet : r = s) :
  (lwhisker (idpath b) bet) = (lunit r)^ @ bet @ (lunit s).
Proof.
  induction r.
  induction bet.
  cbn.
  reflexivity.
Qed.
  

Definition zont1 {A} 
  {a b c : A} {p q : a = b} {r s : b = c} 
  (alph : p = q) (bet : r = s) : p @ r = q @ s :=
  (rwhisker alph r) @ (lwhisker q bet).

Definition zont2 {A} 
  {a b c : A} {p q : a = b} {r s : b = c} 
  (alph : p = q) (bet : r = s) : p @ r = q @ s :=
  (lwhisker p bet) @ (rwhisker alph s).

Definition loop_space {A} (a : A) := a = a.
Definition loop_loop_space {A} (a : A)  := idpath a = idpath a.

Definition zonted {A} {a : A} {p q r s : a = a} (alph : p = q) (bet : r = s)
: (zont1 alph bet) = (zont2 alph bet) .
Proof.
  induction alph.
  induction bet.
  unfold zont1.
  unfold zont2.
  induction r.
  induction p.
  reflexivity.
Qed.

Definition zonter1 {A} {a : A} (alph bet : 1 = 1 :> (a = a)) 
  : (zont1 alph bet) = alph @ bet.
Proof.
  assert ((rwhisker alph (idpath a)) @ (lwhisker (idpath a) bet) = (runit (idpath a))^ @ alph @ (runit (idpath a)) @ (lunit (idpath a))^ @ bet @ (lunit (idpath a))).
  - pose proof (rwhisker_1 (idpath a) (idpath a) alph). 
    pose proof (lwhisker_1 (idpath a) (idpath a) bet).
    pose proof (zont1 X X0).
    cbn in *.
    rewrite concat_pp_p.
    rewrite (concat_pp_p ((1 @ alph) @ 1)).
    rewrite (concat_p_pp 1).
    apply X1.
  - unfold zont1.
    rewrite X.
    cbn.
    pose proof runit alph.
    pose proof lunit alph.
    repeat (try rewrite <- X0; try rewrite <- X1).
    pose proof runit (alph @ bet).
    rewrite <- X2.
    reflexivity.
Qed.

Definition zonter2 {A} {a : A} (alph bet : 1 = 1 :> (a = a))
  : (zont2 alph bet) = bet @ alph.
Proof.
  unfold zont2.
  assert ((lwhisker 1 bet @ rwhisker alph 1) = (lunit 1)^ @ bet @ lunit 1 @ (runit 1)^ @ alph @ runit 1).
  - 
    pose proof (rwhisker_1 (idpath a) (idpath a) alph). 
    pose proof (lwhisker_1 (idpath a) (idpath a) bet).
    pose proof (zont2 X0 X).
    cbn in *.
    repeat rewrite concat_pp_p in *.
    apply X1.
  - rewrite X.
    cbn.
    pose proof runit bet.
    pose proof lunit bet.
    repeat (try rewrite <- X0; try rewrite <- X1).
    pose proof runit (bet @ alph).
    rewrite <- X2.
    reflexivity.
Qed.

Definition eckmann_hilton {A} {a : A} (alph bet : 1 = 1 :> (a = a)) :
  alph @ bet = bet @ alph := (zonter1 _ _)^ @ zonted _ _ @ zonter2 _ _.

(* 2.2 *)
Definition ap {A B : Type} {x y : A} (f : A -> B) (r : x = y)
  : (f(x) = f(y))
:= match r with idpath => 1 end.

Theorem t_2_2_2_i {A B C : Type} {x y z : A} (f : A -> B) (p : x = y) (q : y = z) :
  ap f (p @ q) = ap f p @ ap f q. 
Proof.
  induction p.
  induction q.
  cbn.
  reflexivity.
Qed.

Theorem t_2_2_2_ii {A B C : Type} {x y z : A} (f : A -> B) (p : x = y) :
  ap f p^ = (ap f p)^.
Proof.
  induction p.
  cbn [ap "^"].
  reflexivity.
Qed.

Theorem t_2_2_2_iii {A B C : Type} {x y z : A} (f : A -> B) (g : B -> C) (p : x = y)
: ap g (ap f p) = ap (compose g f) p.
Proof.
  induction p.
  unfold ap.
  reflexivity.
Qed.

Theorem t_2_2_2_iv {A B C : Type} {x y z : A} (f : A -> B) (g : B -> C) (p : x = y)
: ap (fun a:A => a) p = p.
Proof.
  induction p.
  unfold ap.
  reflexivity.
Qed.

Check idmap.
(* 2.3 *)

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y)
: P x -> P y 
:= match p with idpath => idmap end.

Check transport.

Theorem transport_theorem {A : Type} {P : A -> Type} {x y : A} (p : x = y)
: P x -> P y.
Proof.
  Check paths_ind.
  exact (paths_ind 
    x
    (fun (a0 : A) (q : x = a0) => P x -> P a0)
    (fun s => idmap s)
    y p
    ).
Restart.
  induction p.
  Show Proof.
  exact idmap.
Qed.

Print transport.
(*
transport@{u u0} =
fun (A : Type) (P : A -> Type) (x y : A) (p : x = y) =>
match p in (_ = a) return (P x -> P a) with
| 1 => idmap
end
     : forall {A : Type} {P : A -> Type} {x y : A}, x = y -> P x -> P y

Arguments transport {A}%type_scope {P}%function_scope {x y} p%path_scope _


transport_theorem@{u u0} =
fun (A : Type) (P : A -> Type) (x y : A) (p : x = y) =>
paths_rect A x (fun (y0 : A) (_ : x = y0) => P x -> P y0) idmap y p
     : forall {A : Type} {P : A -> Type} {x y : A}, x = y -> P x -> P y

Arguments transport_theorem {A}%type_scope {P}%function_scope 
  {x y} p%path_scope _

 *)
Print transport_theorem.
Print idmap.

(* Path lifting property *)

Definition lift {A : Type} {P : A -> Type} {x y : A} 
(u : P x) (p : x = y)
  : (x, u) = (y, transport (fun _ => P x) p u) 
:= match p with idpath => idpath end.

Print lift.

Definition lift_t {A : Type} {P : A -> Type} {x y : A} {u : P x} (p : x = y)
: (x, u) = (y, (transport _ p) u).
Proof.
  induction p.
  unfold transport.
  reflexivity.
Qed.

Print lift.

Definition apd_t 
  {A : Type} {P : A -> Type} {x y : A} 
  (f : forall x, P x) 
  (p : x = y) 
: ((transport _ p) (f x)) = f y.
Proof.
  induction p.
  unfold transport.
  reflexivity.
Defined.

Definition apd
  {A : Type} {P : A -> Type} {x y : A} 
  (f : forall x, P x) 
  (p : x = y) 
: ((transport _ p) (f x)) = f y
:= match p with idpath => idpath end.

Theorem equal_apd
  {A : Type} {P : A -> Type} {x y : A} (f : forall x, P x) 
  (p : x = y) 
  : apd f p = apd_t f p :> (((transport _ p) (f x)) = f y).
Proof.
  induction p.
  pose proof (apd_t f (idpath x)).
  unfold apd.
  unfold apd_t.
  unfold paths_rect.
  unfold paths_ind.
  reflexivity.
Qed.

Definition transport_const_t {A B : Type} {x y : A} 
(p : x = y) (b : B)  : (transport _ p b) = b.
Proof.
  Check paths_ind.
  exact (paths_ind
    x
    (fun (a0 : A) (q : x = a0) => transport _ q b = b)
    (idpath b)
    y p
    ).

  Restart.

  induction p.
  unfold transport.
  reflexivity.
Qed.

Definition transport_const {A B : Type} {x y : A} 
(p : x = y) (b : B)  : (transport _ p b) = b
:= match p with idpath => idpath end.

Definition apd_transport 
  {A B : Type} {f : A -> B} {x y : A} 
  (p : x = y) 
: apd f p = transport_const p (f x) @ ap f p
:= match p with idpath => idpath end.

Definition qp_lemma
  {A : Type} {P : A -> Type} {x y z : A}
  (p : x = y) (q : y = z) (u : P(x))
: transport _ q ((transport _ p) u) = transport _ (p @ q) u.
Proof.
  Show Proof.
  induction p.
  Show Proof.
  induction q.
  Show Proof.
  unfold transport.
  Show Proof.
  cbn.
  Show Proof.
  
  reflexivity.
Defined.

Check paths_ind.
Check paths_rect.
Print qp_lemma.

Definition transport_1 
  {A : Type} {x : A} {P : A -> Type} (u : P x) : (transport _ 1) u = u := idpath.

Check transport_1.
Print transport_1.
Check idmap.
Check transport.

Definition ap_2 {A B : Type} {x y : A} (f : A -> B) (r : x = y)
  : (f(x) = f(y))
:= match r with idpath => (1 : f _ = f _) end.

Print lift.

Definition qp_lemma_d
  {A : Type} {P : A -> Type} {x y z : A}
  (p : x = y) (q : y = z) (u : P(x))
: transport _ q ((transport _ p) u) = transport _ (p @ q) u
:= 
match q as q0 in (_ = a) 
  return (transport _ q0 (transport _ p u) = transport _ (p @ q0) u) 
  with idpath => 
  match p as p0 in (_ = b)
    return (transport _ 1 (transport _ p0 u) = transport _ (p0 @ 1) u)
    with idpath =>
      idpath
  end
end.

Print qp_lemma_d.


(*
qp_lemma@{u u0 u1} =
fun (A : Type) (P : A -> Type) (x y z : A) (p : x = y) (q : y = z) (u : P x) =>
paths_rect A x
  (fun (y0 : A) (p0 : x = y0) =>
   forall q0 : y0 = z, transport q0 (transport _ p0 u) = transport (p0 @ q0) u)
  (fun q0 : x = z =>
   paths_rect A x
     (fun (z0 : A) (q1 : x = z0) =>
      transport q1 (transport 1 u) = transport (1 @ q1) u)
     (1 : transport 1 (transport 1 u) = transport (1 @ 1) u) z q0)
  y p q

(fun (A : Type) (P : A -> Type) (x y z : A) (p : x = y) (q : y = z) (u : P x) =>
 paths_rect A x
   (fun (y0 : A) (p0 : x = y0) =>
    forall q0 : y0 = z, transport q0 (transport _ p0 u) = transport (p0 @ q0) u)
   (fun q0 : x = z => ?Goal@{q:=q0}) y p q)

 *)

Definition transportconst 
  {A B : Type} {P : A -> Type} {x y : A} 
  (p : x = y) (h : P x = B) (b : B) 
: transport _ p b = b := 
match p with idpath 
  => idpath
end.

Definition l_2_3_10
  {A B : Type} {P : B -> Type} {x y : A} {f : A -> B} 
  (p : x = y) (u : P (f x))
: transport (compose P f) p u = transport P (ap f p) u
:=
match p with idpath
  => idpath
end.

Definition l_2_3_11
  {A : Type} {P Q : A -> Type} {x y : A} {f : forall a, P a -> Q a}
  (p : x = y) (u : P x)
: transport Q p (f x u) = f y (transport P p u)
:= 
match p with idpath
  => idpath
end.

Definition homotope {A} {P : A -> Type} 
(f g : forall x, P x)
: Type := forall x, (f x = g x).

Definition homorefl 
  {A} {P : A -> Type} 
  (f : forall x, P x)
: homotope f f
:= fun x => idpath (f x).

(* when you need a dependent function type out, use fun!
   functions can be used to produce dependent function types *)

Definition homosymm
  {A} {P : A -> Type} 
  (f g : forall x, P x)
: homotope f g -> homotope g f
:= fun h => fun x => (h x)^.

Definition homotrans
  {A} {P : A -> Type} 
  (f g h : forall x, P x)
  : homotope f g -> homotope g h -> homotope f h
:= fun h1 h2 => fun x => (h1 x) @ (h2 x).

Definition l_2_4_3
  {A B : Type} {x y : A} {f g : A -> B} 
  (H : homotope f g) (p : x = y)
: H x @ ap g p = ap f p @ H y
:= 
(* f x = g x @ g x = g y , f x = f y @ f y = g y *)
match p (*as p0 in (_ = y0)*)
(*return H x @ ap g p0 = ap f p0 @ H y0*)
with idpath
=> (runit (H x))^ @ (lunit (H x))
end.

Definition l_2_4_3_t
  {A B : Type} {x y : A} {f g : A -> B} 
  (H : homotope f g) (p : x = y)
: H x @ ap g p = ap f p @ H y.
Proof.
  induction p.
  unfold homotope in *.
  unfold ap.
  rewrite <- lunit.
  rewrite <- runit.
  reflexivity.
Defined.

Print l_2_4_3.



End chapter_2.
