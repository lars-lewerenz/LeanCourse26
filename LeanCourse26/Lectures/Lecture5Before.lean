module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real
noncomputable section
set_option linter.unusedVariables false
variable (a b c : ℝ)

#click_suggestions

/-
# Practical remarks

* You are allowed to hand in homework alone or in pairs of 2.
-/

/- # Last time

Last time we saw:

* Disjunction `A ∨ B`
  - if you have `h : A ∨ B`, use
    `obtain ha | hb := h` to do a case split
  - to prove `A ∨ B`, use `left` or `right` to prove it.

* Negation `¬ A` means `A → False`.

* Main tactics for **Classical logic**:
  - `by_contra h` start a proof by contradiction.
  - `by_cases h : p` to start a proof by cases on statement `p`.
  - `push_neg` to push negations inside quantifiers and connectives.
-/



/- ## Proving two functions are equal
To prove that two functions `f g : α → β` are equal, you can prove
that they are equal at every point, using the `ext` tactic.
`ext x` can prove that `f = g` if `f x = g x` for a new variable `x`.
-/

example {α β : Type*} {f g : α → β} (h : ∀ x, f x = g x) : f = g := by
  ext x
  apply h


-- `rfl` can prove an equality `f = f`,
example : (fun n : ℤ ↦ n + 2) = (fun n : ℤ ↦ n + 2) := rfl

-- but once two functions are not "obviously" equal, you need `ext` to prove it.
example : (fun n : ℤ ↦ n + 2) = (fun n : ℤ ↦ n + 2 + 0) := by
  ext n
  ring

example : (fun n : ℤ ↦ 2 * n + 5) =
    (fun n : ℤ ↦ (n + 2) + (n + 6) - 3) := by
  ext n
  ring






/- # Finding Lemmas

* You can shift-click on subexpressions in the infoview,
  and gives a list of possible lemmas to apply/rewrite there.
  (the command `#click_suggestions` at the top of the file enables this)

* Use tactics with a question mark to find a lemma.
  - `exact?` tries to apply a *single* lemma from the library
    to prove the current goal.
  - `apply?` tries to find all lemmas that can be used with `apply`
    to the current goal.

* Use `#leansearch "<query>."` to query theorems in natural language.
  More results are displayed on the website https://leansearch.net/

* Use https://loogle.lean-lang.org/ or its command
  `#loogle <query>`.

* Guess the name of the lemma
  - When typing a name, a list of suggested completions automatically
    shows up
  - You can also press `ctrl-space` (or `cmd-space` on a Mac)
    to see the list of suggestions.
  - Pressing `ctrl-space` toggles the display of the documentation
    of the selected completion.
  - You can also press `ctrl-T` (or `cmd-T`) to search for a lemma name
    (choosing an option shows you where it is proven)
  - You can search lemmas by name in the API documentation:
    https://leanprover-community.github.io/mathlib4_docs/

  Some naming conventions:
  - a theorem named `A_of_B_of_C` establishes something of the form `A`
    from hypotheses of the form `B` and `C`.
  - `A`, `B`, and `C` approximate the way we might read the statement out loud.
  - Example: a theorem showing `x + y ≤ ...` will probably start with `add_le`.
    After typing `add_le` the autocomplete will give you some helpful choices.

* You can browse Mathlib
If you ctrl-click on a definition or theorem in VS Code you will jump
to the file where the theorem is proven.
Similar theorems are often proven together in the same file.
-/

example (a b c d : ℝ) (hb : 0 < b) :
    b ^ (a * c + d) = (b ^ c) ^ a * b ^ d := by
  sorry


example (a b x y : ℝ) (h : a < b) (h2 : x ≤ y) :
    a + exp x < b + exp y := by
  sorry


lemma cancel_addition (a b c : ℝ) (h : a + b = a + c) : b = c := by
  sorry

lemma cancel_addition' {a b c : ℝ} (h : a + b = a + c) : b = c := by
  sorry

/-
In `cancel_addition` above, the curly braces around `{a b c : ℝ}`
indicate that these arguments are *implicit*:
they don't have to be stated, but will be figured out by Lean automatically.
-/

example {b c : ℝ} (h : 2 + b = 2 + c) : b = c := by
  sorry

/- {G : Type*} and [Group G] are both implicit arguments.
The difference will be discussed later. -/

example {G : Type*} [Group G] (a : G) : a * a⁻¹ = 1 := by
  sorry


/-
the `simp` tactic is used to *simplify* expressions.
`simp?` shows which lemmas are used.
-/

example (x : ℝ) : (3 * (x - x)) ^ 2 = 0 := by
  sorry


/-
# Exercises

Use `#click_suggestions` or other search tools to prove the following
-/

example (a b c d : ℝ) (hb : 0 < b) (h : b ^ d = 2) :
    b ^ (c - a * d) = b ^ c / 2 ^ a := by
  sorry

example (a b c d : ℝ) (hb : 0 < b) (h : b ^ d = 2) :
    sinh (a + 1) + sinh (a - 1) = sinh a * (exp 1 + 1 / exp 1) := by
  sorry



/- # Orders -/

section Real
variable {a b c d e x y z : ℝ}

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_antisymm : a ≤ b → b ≤ a → a = b)


/- We can apply these lemmas manually, or use the `rfl`/`calc` tactics. -/

example (x : ℝ) : x ≤ x := by exact le_refl x
example (x : ℝ) : x ≤ x := by apply le_refl
example (x : ℝ) : x ≤ x := by rfl

example (h₀ : a = b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  sorry

/-
`order` can prove inequalities that only follow from
order-theoretic principles.
-/

example (h₀ : a = b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  sorry

/-
`linarith` can prove inequalities (and equalities)
that follow from linear combinations of assumptions.
-/

example (x y z : ℝ) (hx : x ≤ 3 * y) (h2 : ¬ y > 2 * z)
    (h3 : x ≥ 6 * z) : x = 3 * y := by
  sorry


/- Mathlib has lemmas that all common operations are monotone.
Here are a few examples. -/

#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (mul_le_mul : a ≤ b → c ≤ d → 0 ≤ c → 0 ≤ b → a * c ≤ b * d)
#check (mul_le_mul_of_nonneg_right : b ≤ c → 0 ≤ a → b * a ≤ c * a)

example (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 0 ≤ c) :
    a * (b + 2) ≤ (a + c) * (b + 2) := by
  sorry

/- `gcongr` is very convenient for monotonicity of functions. -/

example (h : a ≤ b) (h2 : b ≤ c) : exp a ≤ exp c := by
  sorry

example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  sorry

example (hac : 0 ≤ a) (hb : 0 ≤ b) (h : 0 ≤ c) :
    a * (b + 2) ≤ (a + c) * (b + 2) := by
  sorry


/- Remark: for equalities, you should use `congr` instead of `gcongr` -/

example (h : a = b) : c - exp b = c - exp a := by
  sorry




/-
`rw` can *only* rewrite with `=` or `↔`.
`grw` can be used to "rewrite" with other relations, like inequalities.

`grw` stands for generalized rewrite.
-/


/-
a ≡ b [ZMOD n] is the congruence relation
defined for triples of integers.
-/

#check 8 ≡ 3 [ZMOD 5]

example {a b n : ℤ} (h : a ≡ b [ZMOD n]) : a ^ 2 ≡ b ^ 2 [ZMOD n] := by
  grw [h]



example {a b c d n : ℤ} (h : a ≡ b [ZMOD n]) (h' : c ≡ d [ZMOD n]) :
    a ^ 2 * c ≡ b ^ 2 * d [ZMOD n] := by
  sorry



example (f g : ℝ → ℝ) (h : ∀ x : ℝ, f x ≤ g x)
    (h₂ : g a + g b ≤ 5) : f a + f b ≤ 5 := by
  sorry


example {a b c d : ℝ} (h₀ : 0 < b) (h₁ : b < a) (h₂ : c ≤ d) :
    1 / a + exp c ≤ exp d + 1 / b := by
  sorry


example {a b c : ℤ} (h₁ : a ∣ b) (h₂ : b ∣ a ^ 2 * c) :
    a ∣ b ^ 2 * c := by
  sorry








/-
We've introduced a lot of tactics.
You can find an overview of common tactics
in the **Tactic cheatsheet** of this repository.
-/



/- # Sets

In set theory you can make sets with arbitrary elements.
In Lean, all sets have to be sets of elements from a specific type.

If `s : Set α` then `s` is a set with elements from `α`.
-/

#check Set ℕ
#check Set ℝ

variable {α β ι : Type*} (x : α) (s t u : Set α)

/- We can talk about membership and (strict) subsets. -/

#check x ∈ s       -- \in or \mem
#check x ∉ s       -- \notin
#check s ⊆ t       -- \sub
#check s ⊂ t       -- \ssub


variable (y : β)

/- You are not allowed to ask if elements
from a different type are in a set. -/
-- #check y ∈ s


/- We have the common set-theoretic operations.
Note: it is important that `s` and `t`
are sets of elements from the *same* type. -/

#check s ∩ t       -- \inter or \cap
#check s ∪ t       -- \union or \cup
#check s \ t       -- the normal symbol `\` on your keyboard,
                   -- (use a space afterwards to not use the unicode-replacement)

#check sᶜ          -- \compl or \^c
#check (∅ : Set α) -- \empty
#check (Set.univ : Set α)

/- If you *open* a namespace, you are able to use names in it
without the prefix. -/

-- #check (univ : Set α)

open Set

#check (univ : Set α)






/- Showing that `x` is an element of
`s ∩ t`, `s ∪ t` or `sᶜ` corresponds by definition
to conjunction, disjunction or negation. -/

#check (mem_inter_iff x s t : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t)
#check (mem_union x s t : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t)
#check (mem_compl_iff s x : x ∈ sᶜ ↔ x ∉ s)
#check (mem_sdiff x : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t)

#check (mem_univ x : x ∈ univ)
#check (notMem_empty x : x ∉ ∅)



/-
There are various ways to prove the following lemmas:
* use lemma `mem_inter_iff`
* use `simp`
* directly apply `constructor`
* give a direct proof: `⟨xs, xt⟩`
-/
example (hxs : x ∈ s) (hxt : x ∈ t) : x ∈ s ∩ t := by
  sorry
  done

example (hxs : x ∈ s) : x ∈ s ∪ t := by
  sorry
  done


example (hx : x ∈ s \ t) : x ∈ (s ∪ t) ∩ (sᶜ ∪ tᶜ) := by
  sorry
  done







/- `s ⊆ t` means that for every element `x` in `s`,
  `x` is also an element in `t`. -/
#check (subset_def : (s ⊆ t) = ∀ x ∈ s, x ∈ t)
-- equivalently, it states: `s ⊆ t ↔ ∀ x, x ∈ s → x ∈ t`

example : s ∩ t ⊆ s ∩ (t ∪ u) := by
  sorry
  done

/- You can also prove it at the level of sets,
without talking about elements. -/
example : s ∩ t ⊆ s ∩ (t ∪ u) := by
  sorry
  done
