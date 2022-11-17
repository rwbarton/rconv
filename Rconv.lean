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

def Nat.sumPrimes (n : Nat) : Nat :=
(Set.range' n).finsum fun i => if i.prime then i else 0

end Theory



section Computation

def Riff (p : Prop) (q : Bool) := p ↔ (q = true)

def Nat.dividesImpl (a b : Nat) : Bool :=
if a == 0
  then b == 0
  else b == a * (b / a)

def Nat.primeImpl (n : Nat) : Bool :=
n > 1 ∧ ! n.any fun i => i > 1 ∧ i.dividesImpl n

axiom Nat.primeImplCorrect (n : Nat) :
  Riff n.prime n.primeImpl

-- #eval ((List.range 100).filter Nat.primeImpl).length

--def Set.range'Impl₂ (n : Nat) : Impl (Set.range' n) (Nat → Bool) := fun i => i ≤ n

def Req {α : Type _} (x y : α) :=
x = y

def RSetAsList {α : Type _} (x : Set α) (y : List α) : Prop :=
y.noDups ∧ y.toSet = x

def RSetAsFunBool {α : Type _} (x : Set α) (y : α → Bool) :=
∀ a, x a ↔ y a

axiom Set.range'Impl₁ (n : Nat) : RSetAsList (Set.range' n) (List.range (n+1))

-- Use this in conjunction with ap rule for ⇒
-- axiom Set.finsumImpl : (RSetAsList ⇒ (Req ⇒ Req) ⇒ Req) (Set.finsum) (λ l g => l.map g |>.sum)
-- to derive the following:

axiom Set.finsumImpl {α : Type _} (s : Set α) (l : List α) (f : α → Nat) (g : α → Nat) :
  RSetAsList s l →
  (∀ j k, Req j k → Req (f j) (g k)) →      -- (Req ⇒ Req) f g
  Req (s.finsum f) (l.map g |>.sum)

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

#print if_classical''

def Req.result {α : Type _} {x y : α} (_ : Req x y) : α := y

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
