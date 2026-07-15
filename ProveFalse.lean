-- I am not the author.
-- https://github.com/leanprover/lean4/pull/8060
import Lean

def g.{u} : PUnit.{u} → Nat := fun _ => open Classical in if Type = Type then 0 else 0

def T : Nat → Prop := (if · = 0 then False else True)

def POW := Nat.pow (g.{0} ⟨⟩) 1

elab "#inject_bad_proof" : command => do
  let decl : Lean.Declaration := .defnDecl {
      name := `mythm,
      hints := .regular 0,
      safety := .safe,
      type := (.app (.const `T []) (.const `POW [])),
      levelParams := [],
      value := (.const `True.intro [])
    }
  Lean.Elab.Command.liftCoreM (Lean.addDecl decl)

#inject_bad_proof

theorem g_eq_zero {n : PUnit} : g.{u} n = 0 := by
  unfold g
  split <;> rfl

theorem show_false : False := by
  change T (Nat.pow 0 1)
  exact g_eq_zero ▸ mythm

#print axioms show_false

example : 1 + 1 = 3 :=
  show_false.elim
