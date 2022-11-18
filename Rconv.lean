import Lean.Elab.Tactic

set_option autoImplicit false

noncomputable section Theory    -- :)

open Classical

def Set (α : Type _) : Type _ :=
α → Prop

def Set.range' (n : Nat) : Set Nat :=
fun i => i ≤ n

def Nat.divides (a b : Nat) : Prop :=
∃ k, a * k = b

def Nat.prime (n : Nat) : Prop :=
n ≠ 1 ∧ ∀ a b, n.divides (a * b) → n.divides a ∨ n.divides b

def List.noDups {α : Type _} : List α → Prop
| [] => True
| (x :: xs) => x ∉ xs ∧ xs.noDups

def List.toSet {α : Type _} (l : List α) : Set α :=
fun x => x ∈ l

def List.sum : List Nat → Nat
| [] => 0
| (x :: xs) => x + xs.sum

def Set.finsum {α : Type _} (s : Set α) (f : α → Nat) : Nat :=
if h : ∃ (l : List α), l.noDups ∧ l.toSet = s
then ((choose h).map f).sum
else 0

def cite {α : Type _} (p : Prop) (x y : α) : α :=
if p then x else y

@[inherit_doc ite] syntax (name := termCIfThenElse)
  ppRealGroup(ppRealFill(ppIndent("cif " term " then") ppSpace term)
    ppDedent(ppSpace) ppRealFill("else " term)) : term

macro_rules
  | `(cif $c then $t else $e) => do
    let mvar ← Lean.withRef c `(?m)
    `(let_mvar% ?m := $c; wait_if_type_mvar% ?m; cite $mvar $t $e)

def Nat.sumPrimes (n : Nat) : Nat :=
(Set.range' n).finsum fun i => cif i.prime then i else 0

end Theory



section Computation

def Req {α : Type _} (x y : α) :=
x = y

def Riff (p : Prop) (q : Bool) := p ↔ (q = true)

def Rfun {α α' β β'} (R : α → β → Prop) (R' : α' → β' → Prop) : (α → α') → (β → β') → Prop :=
fun f g => ∀ ⦃a b⦄, R a b → R' (f a) (g b)

infixr:50 " ⇨ " => Rfun

def Nat.dividesImpl (a b : Nat) : Bool :=
if a == 0
  then b == 0
  else b == a * (b / a)

def Nat.primeImpl (n : Nat) : Bool :=
n > 1 ∧ ! n.any fun i => i > 1 ∧ i.dividesImpl n

axiom Nat.primeImplCorrect (n : Nat) :
  Riff n.prime n.primeImpl

axiom RprimeImpl : (Req ⇨ Riff) Nat.prime Nat.primeImpl

-- #eval ((List.range 100).filter Nat.primeImpl).length

--def Set.range'Impl₂ (n : Nat) : Impl (Set.range' n) (Nat → Bool) := fun i => i ≤ n

def RSetAsList {α : Type _} (x : Set α) (y : List α) : Prop :=
y.noDups ∧ y.toSet = x

def RSetAsFunBool {α : Type _} (x : Set α) (y : α → Bool) :=
∀ a, x a ↔ y a

def Rdepfun {α β : Type _} {α' : α → Type _} {β' : β → Type _}
  (R : α → β → Prop) (R' : (a : α) → (b : β) → α' a → β' b → Prop) : ((a : α) → α' a) → ((b : β) → β' b) → Prop :=
fun f g => ∀ ⦃a b⦄, R a b → R' a b (f a) (g b)

infixr:50 " ⇨ᵈ " => Rdepfun

theorem Rap {α α' β β'} {R : α → β → Prop} {R' : α' → β' → Prop}
  {f : α → α'} (g : β → β') {x : α} (y : β) :
  (R ⇨ R') f g → R x y → R' (f x) (g y) :=
fun h₁ h₂ => h₁ h₂

theorem RAP {Α Α' Β Β'} {r : Α → Β → Prop} {r' : Α' → Β' → Prop}
  {F : Α → Α'} (G : Β → Β') {X : Α} (Y : Β) :
  (r ⇨ r') F G → r X Y → r' (F X) (G Y) :=
fun H₁ H₂ => H₁ H₂

axiom Set.range'Impl₁ (n : Nat) : RSetAsList (Set.range' n) (List.range (n+1))

-- Use this in conjunction with ap rule for ⇒
-- axiom Set.finsumImpl : (RSetAsList ⇒ (Req ⇒ Req) ⇒ Req) (Set.finsum) (λ l g => l.map g |>.sum)
-- to derive the following:

axiom Set.finsumImpl {α : Type _} (s : Set α) (l : List α) (f : α → Nat) (g : α → Nat) :
  RSetAsList s l →
  (∀ j k, Req j k → Req (f j) (g k)) →      -- (Req ⇒ Req) f g
  Req (s.finsum f) (l.map g |>.sum)

theorem Set.finsumImpl₀ {α : Type _} :
  (RSetAsList ⇨ (Req ⇨ Req) ⇨ Req) (@Set.finsum (α := α)) (λ l g => l.map g |>.sum) :=
by
  intro s s' hs f f' hf
  apply Set.finsumImpl <;> assumption

theorem if_classical {p : Prop} {hp : Decidable p} [hp' : Decidable p] {α : Type _} (x y : α) :
  @ite α p hp x y = @ite α p hp' x y :=
by
  have : hp = hp' := Subsingleton.elim _ _
  rw [this]

axiom if_classical' {p : Prop} (p' : Prop) {hp : Decidable p} (hp' : Decidable p') {α : Type _} (x y : α) :
  (p ↔ p') →
  Req (if p then x else y) (if p' then x else y)

-- TODO: Generalize x, y to x', y' on RHS
-- axiom _ : (Riff ⇒ Req ⇒ Req ⇒ Req) ite (λ p' x y, if p' then x else y)
-- axiom _ {R} : (Riff ⇒ R ⇒ R ⇒ R) ite (λ p' x y, if p' then x else y)
axiom if_classical'' {p : Prop} (p' : Bool) {hp : Decidable p} {α : Type _} (x y : α) :
  Riff p p' →
  Req (if p then x else y) (if p' then x else y)

def id2 {α β} : (α → β) → α → β := id

def Rtriv (α β : Type _) (x : α) (y : β) : Prop := True

axiom Rcite {α β} {R : α → β → Prop} :
  (Riff ⇨ R ⇨ R ⇨ R) cite cond

def BLAH {α β} (f : (α → β) → Sort _) (x : α → β) : f (λ i => x i) → f x := id
def BLAH2 {α β} (f : β → Sort _) (y : α → β) (z : α) : f (y z) → f (y z) := id

def CHANGE (α) : α → α := id

--axiom if_classical₀ {α β} {R : α → β → Prop} :
--  (Riff ⇨ R ⇨ R ⇨ R) (open Classical in fun p x y => if p then x else y) (fun b x y => if b then x else y)

#print if_classical''




def Req.result {α : Type _} {x y : α} (_ : Req x y) : α := y

section

open Lean.Meta Lean.Elab.Tactic

elab "assign " n:term " => " e:term : tactic =>
  Lean.Elab.Tactic.withMainContext do
    match (← elabTerm n none) with
    | .mvar m => m.withContext do
      m.assign (← elabTerm e none)
      return ()
    | _ => return ()

end

def Nat.sumPrimesImpl₁ (n : Nat) : Nat :=
by
  have : Req (Nat.sumPrimes n) ?y1 :=
  by
    unfold Nat.sumPrimes
    -- TODO: megahack.
    -- Version that worked: explicitly write the correct formula in place of ?RESULT.
    -- Versions that didn't work: all others.
    refine' Rap (R := Req ⇨ Req) ?fx (?RESULT) ?rfx ?ry
    case rfx =>
      refine' Rap (R := RSetAsList) ?_ ?_ ?rf ?rx
      case rf => refine' Set.finsumImpl₀
      case rx => refine' Set.range'Impl₁ _
    case ry =>
      -- refine_to_fun RESULT
      -- assign ?RESULT => (fun j => (?RESULT' : ?_ → ?_) ?_)
      let M1 : Nat → Nat → Nat := fun j => cond (primeImpl j) j
      let M2 : Nat → Nat := fun j => j
      intro j j' hj
      dsimp only
      refine CHANGE (Req (cite (prime j) j 0) (M1 j' (M2 j'))) ?_
      set_option pp.all true in
      refine' Rap (R := Req) (R' := Req) _ _ ?rg ?rz₁
      case rg =>
        refine' Rap (R := Req) (R' := Req ⇨ Req) ?g₁ ?z₂ ?rg₁ ?rz₂
        case rg₁ =>
          refine' Rap ?_ ?_ ?rg₂ ?rz₃
          case rg₂ => exact Rcite
          case rz₃ =>
            refine' RprimeImpl ?_
            assumption
        case rz₂ =>
          assumption
      case rz₁ =>
        rfl
    -- refine Set.finsumImpl _ ?_ _ ?_ ?rs ?rf
    -- case rs =>
    --   refine Set.range'Impl₁ _
    -- case rf =>
    --   intro j k h
    --   subst h
    --   refine if_classical'' ?_ _ _ ?rp
    --   case rp =>
    --     refine (Nat.primeImplCorrect j)
  exact ?y1
  -- -- exact this.result

#eval Nat.sumPrimesImpl₁ 5
#print Nat.sumPrimesImpl₁

#exit

def Nat.sumPrimesImpl' (n : Nat) : Nat :=
by
  have : Req (Nat.sumPrimes n) ?y :=
  by
    unfold sumPrimes
    refine Set.finsumImpl _ ?_ _ ?_ ?rs ?rf
    case rs =>
      refine Set.range'Impl₁ _
    case rf =>
      intro j k h
      subst h
      refine if_classical'' ?_ _ _ ?rp
      case rp =>
        refine (Nat.primeImplCorrect j)
  exact ?y
  -- exact this.result

#print Nat.sumPrimesImpl'
#eval Nat.sumPrimesImpl' 5000


def Nat.sumPrimesImpl'' (n : Nat) : { y : Nat // Req (n.sumPrimes) y } :=
by
  refine ⟨?_, ?r⟩
  case r =>
    unfold sumPrimes
    refine Set.finsumImpl _ ?_ _ ?_ ?rs ?rf
    case rs =>
      refine Set.range'Impl₁ _
    case rf =>
      intro j k h
      subst h
      refine if_classical'' ?_ _ _ ?rp
      case rp =>
        refine (Nat.primeImplCorrect j)

abbrev Impl {α : Type _} (_a : α) : Type _ := α

def Impl.done {α : Type _} (a : α) : Impl a := a

def Nat.sumPrimesFun (n : Nat) : Nat :=
by
  have t : Impl (Nat.sumPrimesImpl'' n).val :=
  by
    dsimp only [Nat.sumPrimesImpl'']
    apply Impl.done
  exact t

def Nat.sumPrimesFun' (n : Nat) : Nat :=
by
  have : (Nat.sumPrimesImpl'' n).val = ?y :=
  by
    dsimp only [Nat.sumPrimesImpl'']
    exact rfl
  clear this
  exact ?y

theorem works (n : Nat) : Req n.sumPrimes n.sumPrimesFun' :=
(Nat.sumPrimesImpl'' n).property

#print Nat.sumPrimesFun'
#eval Nat.sumPrimesFun 500

end Computation
