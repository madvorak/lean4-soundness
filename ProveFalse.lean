-- https://github.com/leanprover/lean4/pull/14807/
-- https://gitlab.com/-/snippets/6035570

instance True_setoid : Setoid True where
  r := (· = ·)
  iseqv.refl _ := rfl
  iseqv.symm _ := rfl
  iseqv.trans _ _ := rfl

def True_mod_eq := Quotient True_setoid

set_option linter.defProp false

def img_true : True_mod_eq := Quot.mk (· = ·) trivial

opaque opaque_img_true : True_mod_eq := img_true

def mk42 (e : True_mod_eq) : Nat := Quot.lift (fun _ => 42) (fun _ _ _ => rfl) e

def a := mk42 img_true
def b := mk42 opaque_img_true
def c := 42

def P : Prop := a = b
def Q : Prop := c = b

#check (fun (_ : P) => rfl : forall p:P, p = rfl)

opaque q : Q := by
  unfold Q
  have e : c = a := by rfl
  rw [e]
  rfl

def prop_if_h_DEFEQ_rfl (h : P) : Type :=
  Eq.rec (motive := fun _ _ => Type) Prop h

inductive I : forall (h : P), prop_if_h_DEFEQ_rfl h where
| mk : forall (h : P), Bool -> I h

def asProp : forall (_ : P), Sort 0 := λ (h : P) => I h
def Yes_Iq_is_a_Prop : Sort 0 := asProp q

def observe : forall (_h : Yes_Iq_is_a_Prop), Bool :=
  fun (h : Yes_Iq_is_a_Prop) =>
    by
      unfold Yes_Iq_is_a_Prop asProp at h
      exact (h.1)

def mkI : forall (p : P), Bool -> I p := fun p b => .mk p b
def mkI_of_true : Yes_Iq_is_a_Prop := mkI q true
def mkI_of_false : Yes_Iq_is_a_Prop := mkI q false

theorem true_eq_false : true = false := by
  have h : (true = observe mkI_of_true) := by rfl
  have h' : (mkI_of_true = mkI_of_false) := by rfl
  rw [h]
  rw [h']
  rfl

def big_bool_elim (b : Bool) := Bool.rec (motive := fun _ => Prop) False True b

theorem boom : False :=
  @Eq.rec Bool true (motive := fun b _ => big_bool_elim b) True.intro false true_eq_false

#print axioms boom
