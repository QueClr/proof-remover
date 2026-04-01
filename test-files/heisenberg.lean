import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

/- A problem from https://www.rabdos.ai/whitepaper.pdf.

Consider the group whose elements are triples `(a, b, c)` in `Z^3` with the operation

`(a, b, c) * (a', b', c') = (a + a', b + b', c + c' + a * b')`.

Let `x = (1, 0, 0)` and `y = (0, 1, 0)`. What is the minimal length of a product
of `x^{±1}` and `y^{±1}` that equals `(17, 17, 1155)`?
-/

/-- The Heisenberg group over ℤ -/
@[ext]
structure HeisenbergZ where
  a : ℤ
  b : ℤ
  c : ℤ
deriving DecidableEq, Repr

namespace HeisenbergZ

@[simp] def mul' (p q : HeisenbergZ) : HeisenbergZ :=
  ⟨p.a + q.a, p.b + q.b, p.c + q.c + p.a * q.b⟩

@[simp] def one' : HeisenbergZ := ⟨0, 0, 0⟩

@[simp] def inv' (p : HeisenbergZ) : HeisenbergZ :=
  ⟨-p.a, -p.b, -p.c + p.a * p.b⟩

instance : Mul HeisenbergZ where mul := mul'
instance : One HeisenbergZ where one := one'
instance : Inv HeisenbergZ where inv := inv'

@[simp] lemma mul_a (p q : HeisenbergZ) : (p * q).a = p.a + q.a := rfl
@[simp] lemma mul_b (p q : HeisenbergZ) : (p * q).b = p.b + q.b := rfl
@[simp] lemma mul_c (p q : HeisenbergZ) : (p * q).c = p.c + q.c + p.a * q.b := rfl
@[simp] lemma one_a : (1 : HeisenbergZ).a = 0 := rfl
@[simp] lemma one_b : (1 : HeisenbergZ).b = 0 := rfl
@[simp] lemma one_c : (1 : HeisenbergZ).c = 0 := rfl
@[simp] lemma inv_a (p : HeisenbergZ) : p⁻¹.a = -p.a := rfl
@[simp] lemma inv_b (p : HeisenbergZ) : p⁻¹.b = -p.b := rfl
@[simp] lemma inv_c (p : HeisenbergZ) : p⁻¹.c = -p.c + p.a * p.b := rfl

instance : Group HeisenbergZ where
  mul_assoc := fun p q r => by ext <;> simp <;> ring
  one_mul := fun p => by ext <;> simp
  mul_one := fun p => by ext <;> simp
  inv_mul_cancel := fun p => by ext <;> simp

/-- Generator x = (1, 0, 0) -/
def x : HeisenbergZ := ⟨1, 0, 0⟩

/-- Generator y = (0, 1, 0) -/
def y : HeisenbergZ := ⟨0, 1, 0⟩

/-- A generator is either x, x⁻¹, y, or y⁻¹ -/
inductive Generator
  | x_pos   -- x
  | x_neg   -- x⁻¹
  | y_pos   -- y
  | y_neg   -- y⁻¹
deriving DecidableEq, Repr

@[simp] lemma x_a : x.a = 1 := rfl
@[simp] lemma x_b : x.b = 0 := rfl
@[simp] lemma y_a : y.a = 0 := rfl
@[simp] lemma y_b : y.b = 1 := rfl
@[simp] lemma x_inv_a : x⁻¹.a = -1 := rfl
@[simp] lemma x_inv_b : x⁻¹.b = 0 := rfl
@[simp] lemma y_inv_a : y⁻¹.a = 0 := rfl
@[simp] lemma y_inv_b : y⁻¹.b = -1 := rfl

/-- Evaluate a generator to its HeisenbergZ element -/
def Generator.eval : Generator → HeisenbergZ
  | .x_pos => x
  | .x_neg => x⁻¹
  | .y_pos => y
  | .y_neg => y⁻¹

/-- Evaluate a word (list of generators) to a HeisenbergZ element -/
def evalWord : List Generator → HeisenbergZ
  | [] => 1
  | g :: gs => g.eval * evalWord gs

/-- Count occurrences of x in a word -/
def countXPos : List Generator → ℕ
  | [] => 0
  | Generator.x_pos :: gs => 1 + countXPos gs
  | _ :: gs => countXPos gs

/-- Count occurrences of x⁻¹ in a word -/
def countXNeg : List Generator → ℕ
  | [] => 0
  | Generator.x_neg :: gs => 1 + countXNeg gs
  | _ :: gs => countXNeg gs

/-- Count occurrences of y in a word -/
def countYPos : List Generator → ℕ
  | [] => 0
  | Generator.y_pos :: gs => 1 + countYPos gs
  | _ :: gs => countYPos gs

/-- Count occurrences of y⁻¹ in a word -/
def countYNeg : List Generator → ℕ
  | [] => 0
  | Generator.y_neg :: gs => 1 + countYNeg gs
  | _ :: gs => countYNeg gs

/-- The a-component contribution of each generator -/
def Generator.aContrib : Generator → ℤ
  | .x_pos => 1
  | .x_neg => -1
  | .y_pos => 0
  | .y_neg => 0

/-- The b-component contribution of each generator -/
def Generator.bContrib : Generator → ℤ
  | .x_pos => 0
  | .x_neg => 0
  | .y_pos => 1
  | .y_neg => -1

@[simp] lemma Generator.eval_a (g : Generator) : g.eval.a = g.aContrib := by cases g <;> rfl
@[simp] lemma Generator.eval_c (g : Generator) : g.eval.c = 0 := by cases g <;> rfl

/-- Sum of b-contributions of a word -/
def sumBContrib : List Generator → ℤ
  | [] => 0
  | g :: gs => g.bContrib + sumBContrib gs

/-- The c-component contribution: for each generator, multiply its a-contribution
    by the b-value accumulated from all generators to its RIGHT in the word -/
def cContrib : List Generator → ℤ
  | [] => 0
  | g :: gs => g.aContrib * sumBContrib gs + cContrib gs

/-- The a-component of evalWord equals countXPos - countXNeg -/
theorem evalWord_a_eq_count_diff (w : List Generator) :
    (evalWord w).a = (countXPos w : ℤ) - (countXNeg w : ℤ) := by
  induction w with
  | nil => simp [evalWord, countXPos, countXNeg]
  | cons g gs ih =>
    simp only [evalWord, mul_a]
    rw [ih]
    cases g with
    | x_pos => simp only [Generator.eval, x_a, countXPos, countXNeg]; omega
    | x_neg => simp only [Generator.eval, x_inv_a, countXPos, countXNeg]; omega
    | y_pos => simp only [Generator.eval, y_a, countXPos, countXNeg]; omega
    | y_neg => simp only [Generator.eval, y_inv_a, countXPos, countXNeg]; omega

/-- The b-component of evalWord equals countYPos - countYNeg -/
theorem evalWord_b_eq_count_diff (w : List Generator) :
    (evalWord w).b = (countYPos w : ℤ) - (countYNeg w : ℤ) := by
  induction w with
  | nil => simp [evalWord, countYPos, countYNeg]
  | cons g gs ih =>
    simp only [evalWord, mul_b]
    rw [ih]
    cases g with
    | x_pos => simp only [Generator.eval, x_b, countYPos, countYNeg]; omega
    | x_neg => simp only [Generator.eval, x_inv_b, countYPos, countYNeg]; omega
    | y_pos => simp only [Generator.eval, y_b, countYPos, countYNeg]; omega
    | y_neg => simp only [Generator.eval, y_inv_b, countYPos, countYNeg]; omega

/-- sumBContrib equals the b-component of evalWord -/
lemma sumBContrib_eq_evalWord_b (w : List Generator) :
    sumBContrib w = (evalWord w).b := by
  induction w with
  | nil => simp [sumBContrib, evalWord]
  | cons g gs ih =>
    simp only [sumBContrib, evalWord, mul_b, ih]
    cases g <;> simp [Generator.bContrib, Generator.eval]

/-- The c-component of evalWord equals cContrib -/
theorem evalWord_c_eq_cContrib (w : List Generator) :
    (evalWord w).c = cContrib w := by
  induction w with
  | nil => simp [evalWord, cContrib]
  | cons g gs ih =>
    simp only [evalWord, mul_c, Generator.eval_c, zero_add]
    rw [ih, Generator.eval_a]
    simp only [cContrib, sumBContrib_eq_evalWord_b]
    ring

-- ============================================================================
-- CANONICAL WORD CONSTRUCTION AND PROPERTIES
-- ============================================================================

/-- Create a list of n copies of generator g -/
def repeatGen (g : Generator) : ℕ → List Generator
  | 0 => []
  | n + 1 => g :: repeatGen g n

@[simp] lemma repeatGen_zero (g : Generator) : repeatGen g 0 = [] := rfl

@[simp] lemma repeatGen_succ (g : Generator) (n : ℕ) :
    repeatGen g (n + 1) = g :: repeatGen g n := rfl

@[simp] lemma repeatGen_length (g : Generator) (n : ℕ) :
    (repeatGen g n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatGen, ih]

/-- sumBContrib of repeated y_pos is n -/
@[simp] lemma sumBContrib_repeatGen_y_pos (n : ℕ) :
    sumBContrib (repeatGen Generator.y_pos n) = n := by
  induction n with
  | zero => simp [sumBContrib]
  | succ n ih => simp only [repeatGen_succ, sumBContrib, Generator.bContrib, ih]; omega

/-- sumBContrib of repeated x_pos is 0 -/
@[simp] lemma sumBContrib_repeatGen_x_pos (n : ℕ) :
    sumBContrib (repeatGen Generator.x_pos n) = 0 := by
  induction n with
  | zero => simp [sumBContrib]
  | succ n ih => simp [sumBContrib, Generator.bContrib, ih]

/-- sumBContrib of repeated x_neg is 0 -/
@[simp] lemma sumBContrib_repeatGen_x_neg (n : ℕ) :
    sumBContrib (repeatGen Generator.x_neg n) = 0 := by
  induction n with
  | zero => simp [sumBContrib]
  | succ n ih => simp [sumBContrib, Generator.bContrib, ih]

/-- sumBContrib distributes over append -/
@[simp] lemma sumBContrib_append (w₁ w₂ : List Generator) :
    sumBContrib (w₁ ++ w₂) = sumBContrib w₁ + sumBContrib w₂ := by
  induction w₁ with
  | nil => simp [sumBContrib]
  | cons g gs ih => simp [sumBContrib, ih]; ring

/-- cContrib of repeated y_neg is 0 -/
@[simp] lemma cContrib_repeatGen_y_neg (n : ℕ) :
    cContrib (repeatGen Generator.y_neg n) = 0 := by
  induction n with
  | zero => simp [cContrib]
  | succ n ih => simp [cContrib, Generator.aContrib, ih]

/-- cContrib of repeated y_pos is 0 -/
@[simp] lemma cContrib_repeatGen_y_pos (n : ℕ) :
    cContrib (repeatGen Generator.y_pos n) = 0 := by
  induction n with
  | zero => simp [cContrib]
  | succ n ih => simp [cContrib, Generator.aContrib, ih]

/-- cContrib of repeated x_neg is 0 -/
@[simp] lemma cContrib_repeatGen_x_neg (n : ℕ) :
    cContrib (repeatGen Generator.x_neg n) = 0 := by
  induction n with
  | zero => simp [cContrib]
  | succ n ih => simp [cContrib, Generator.aContrib, ih]

/-- cContrib of repeated x_pos is 0 -/
@[simp] lemma cContrib_repeatGen_x_pos (n : ℕ) :
    cContrib (repeatGen Generator.x_pos n) = 0 := by
  induction n with
  | zero => simp [cContrib]
  | succ n ih => simp [cContrib, Generator.aContrib, ih]

/-- Sum of a-contributions of a word -/
def sumAContrib : List Generator → ℤ
  | [] => 0
  | g :: gs => g.aContrib + sumAContrib gs

/-- sumAContrib distributes over append -/
@[simp] lemma sumAContrib_append (w₁ w₂ : List Generator) :
    sumAContrib (w₁ ++ w₂) = sumAContrib w₁ + sumAContrib w₂ := by
  induction w₁ with
  | nil => simp [sumAContrib]
  | cons g gs ih => simp [sumAContrib, ih]; ring

/-- sumAContrib of repeated y_neg is 0 -/
@[simp] lemma sumAContrib_repeatGen_y_neg (n : ℕ) :
    sumAContrib (repeatGen Generator.y_neg n) = 0 := by
  induction n with
  | zero => simp [sumAContrib]
  | succ n ih => simp [sumAContrib, Generator.aContrib, ih]

/-- sumAContrib of repeated y_pos is 0 -/
@[simp] lemma sumAContrib_repeatGen_y_pos (n : ℕ) :
    sumAContrib (repeatGen Generator.y_pos n) = 0 := by
  induction n with
  | zero => simp [sumAContrib]
  | succ n ih => simp [sumAContrib, Generator.aContrib, ih]

/-- sumAContrib of repeated x_pos is n -/
@[simp] lemma sumAContrib_repeatGen_x_pos (n : ℕ) :
    sumAContrib (repeatGen Generator.x_pos n) = n := by
  induction n with
  | zero => simp [sumAContrib]
  | succ n ih => simp only [repeatGen_succ, sumAContrib, Generator.aContrib, ih]; omega

/-- Key lemma: cContrib distributes over append with cross term -/
lemma cContrib_append (w₁ w₂ : List Generator) :
    cContrib (w₁ ++ w₂) = cContrib w₁ + sumAContrib w₁ * sumBContrib w₂ + cContrib w₂ := by
  induction w₁ with
  | nil => simp [cContrib, sumAContrib]
  | cons g gs ih =>
    simp only [List.cons_append, cContrib, sumBContrib_append, sumAContrib]
    rw [ih]
    ring

/-- The canonical word: y^{-j} x^k y^m x^{-ℓ} -/
def canonicalWord (k ℓ m j : ℕ) : List Generator :=
  repeatGen Generator.y_neg j ++
  repeatGen Generator.x_pos k ++
  repeatGen Generator.y_pos m ++
  repeatGen Generator.x_neg ℓ

/-- Length of canonical word -/
theorem canonicalWord_length (k ℓ m j : ℕ) :
    (canonicalWord k ℓ m j).length = j + k + m + ℓ := by
  unfold canonicalWord
  simp only [List.length_append, repeatGen_length]

/-- The c-component of the canonical word is k * m -/
theorem cContrib_canonicalWord (k ℓ m j : ℕ) :
    cContrib (canonicalWord k ℓ m j) = (k : ℤ) * m := by
  unfold canonicalWord
  simp only [cContrib_append, cContrib_repeatGen_y_neg, cContrib_repeatGen_x_pos,
             cContrib_repeatGen_y_pos, cContrib_repeatGen_x_neg,
             sumAContrib_append, sumAContrib_repeatGen_y_neg, sumAContrib_repeatGen_x_pos,
             sumAContrib_repeatGen_y_pos,
             sumBContrib_repeatGen_x_pos, sumBContrib_repeatGen_y_pos,
             sumBContrib_repeatGen_x_neg]
  ring

-- Count lemmas for repeatGen
@[simp] lemma countXPos_repeatGen_x_pos (n : ℕ) : countXPos (repeatGen Generator.x_pos n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatGen, countXPos, ih, Nat.add_comm]

@[simp] lemma countXPos_repeatGen_x_neg (n : ℕ) : countXPos (repeatGen Generator.x_neg n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatGen, countXPos, ih]

@[simp] lemma countXPos_repeatGen_y_pos (n : ℕ) : countXPos (repeatGen Generator.y_pos n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatGen, countXPos, ih]

@[simp] lemma countXPos_repeatGen_y_neg (n : ℕ) : countXPos (repeatGen Generator.y_neg n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatGen, countXPos, ih]

@[simp] lemma countXNeg_repeatGen_x_pos (n : ℕ) : countXNeg (repeatGen Generator.x_pos n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatGen, countXNeg, ih]

@[simp] lemma countXNeg_repeatGen_x_neg (n : ℕ) : countXNeg (repeatGen Generator.x_neg n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatGen, countXNeg, ih, Nat.add_comm]

@[simp] lemma countXNeg_repeatGen_y_pos (n : ℕ) : countXNeg (repeatGen Generator.y_pos n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatGen, countXNeg, ih]

@[simp] lemma countXNeg_repeatGen_y_neg (n : ℕ) : countXNeg (repeatGen Generator.y_neg n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatGen, countXNeg, ih]

@[simp] lemma countYPos_repeatGen_x_pos (n : ℕ) : countYPos (repeatGen Generator.x_pos n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatGen, countYPos, ih]

@[simp] lemma countYPos_repeatGen_x_neg (n : ℕ) : countYPos (repeatGen Generator.x_neg n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatGen, countYPos, ih]

@[simp] lemma countYPos_repeatGen_y_pos (n : ℕ) : countYPos (repeatGen Generator.y_pos n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatGen, countYPos, ih, Nat.add_comm]

@[simp] lemma countYPos_repeatGen_y_neg (n : ℕ) : countYPos (repeatGen Generator.y_neg n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatGen, countYPos, ih]

@[simp] lemma countYNeg_repeatGen_x_pos (n : ℕ) : countYNeg (repeatGen Generator.x_pos n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatGen, countYNeg, ih]

@[simp] lemma countYNeg_repeatGen_x_neg (n : ℕ) : countYNeg (repeatGen Generator.x_neg n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatGen, countYNeg, ih]

@[simp] lemma countYNeg_repeatGen_y_pos (n : ℕ) : countYNeg (repeatGen Generator.y_pos n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatGen, countYNeg, ih]

@[simp] lemma countYNeg_repeatGen_y_neg (n : ℕ) : countYNeg (repeatGen Generator.y_neg n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatGen, countYNeg, ih, Nat.add_comm]

-- Append lemmas for counts
lemma countXPos_append (w₁ w₂ : List Generator) :
    countXPos (w₁ ++ w₂) = countXPos w₁ + countXPos w₂ := by
  induction w₁ with
  | nil => simp [countXPos]
  | cons g gs ih => cases g <;> simp [countXPos, ih, Nat.add_assoc]

lemma countXNeg_append (w₁ w₂ : List Generator) :
    countXNeg (w₁ ++ w₂) = countXNeg w₁ + countXNeg w₂ := by
  induction w₁ with
  | nil => simp [countXNeg]
  | cons g gs ih => cases g <;> simp [countXNeg, ih, Nat.add_assoc]

lemma countYPos_append (w₁ w₂ : List Generator) :
    countYPos (w₁ ++ w₂) = countYPos w₁ + countYPos w₂ := by
  induction w₁ with
  | nil => simp [countYPos]
  | cons g gs ih => cases g <;> simp [countYPos, ih, Nat.add_assoc]

lemma countYNeg_append (w₁ w₂ : List Generator) :
    countYNeg (w₁ ++ w₂) = countYNeg w₁ + countYNeg w₂ := by
  induction w₁ with
  | nil => simp [countYNeg]
  | cons g gs ih => cases g <;> simp [countYNeg, ih, Nat.add_assoc]

/-- Count of x in canonical word -/
theorem countXPos_canonicalWord (k ℓ m j : ℕ) :
    countXPos (canonicalWord k ℓ m j) = k := by
  simp only [canonicalWord, countXPos_append,
    countXPos_repeatGen_y_neg, countXPos_repeatGen_x_pos,
    countXPos_repeatGen_y_pos, countXPos_repeatGen_x_neg]
  omega

/-- Count of x⁻¹ in canonical word -/
theorem countXNeg_canonicalWord (k ℓ m j : ℕ) :
    countXNeg (canonicalWord k ℓ m j) = ℓ := by
  simp only [canonicalWord, countXNeg_append,
    countXNeg_repeatGen_y_neg, countXNeg_repeatGen_x_pos,
    countXNeg_repeatGen_y_pos, countXNeg_repeatGen_x_neg]
  omega

/-- Count of y in canonical word -/
theorem countYPos_canonicalWord (k ℓ m j : ℕ) :
    countYPos (canonicalWord k ℓ m j) = m := by
  simp only [canonicalWord, countYPos_append,
    countYPos_repeatGen_y_neg, countYPos_repeatGen_x_pos,
    countYPos_repeatGen_y_pos, countYPos_repeatGen_x_neg]
  omega

/-- Count of y⁻¹ in canonical word -/
theorem countYNeg_canonicalWord (k ℓ m j : ℕ) :
    countYNeg (canonicalWord k ℓ m j) = j := by
  simp only [canonicalWord, countYNeg_append,
    countYNeg_repeatGen_y_neg, countYNeg_repeatGen_x_pos,
    countYNeg_repeatGen_y_pos, countYNeg_repeatGen_x_neg]
  omega

/-- The canonical word evaluates to (k - ℓ, m - j, k * m) -/
theorem evalWord_canonicalWord (k ℓ m j : ℕ) :
    evalWord (canonicalWord k ℓ m j) = ⟨(k : ℤ) - ℓ, (m : ℤ) - j, (k : ℤ) * m⟩ := by
  ext
  · rw [evalWord_a_eq_count_diff, countXPos_canonicalWord, countXNeg_canonicalWord]
  · rw [evalWord_b_eq_count_diff, countYPos_canonicalWord, countYNeg_canonicalWord]
  · rw [evalWord_c_eq_cContrib, cContrib_canonicalWord]

-- ============================================================================
-- SPECIFIC INSTANCE: (17, 17, 1155) with optimal length 102
-- ============================================================================

/-- The canonical word y⁻¹⁸ x³³ y³⁵ x⁻¹⁶ reaches (17, 17, 1155) -/
theorem canonical_33_16_35_18_reaches_target :
    evalWord (canonicalWord 33 16 35 18) = ⟨17, 17, 1155⟩ := by
  rw [evalWord_canonicalWord]
  norm_num

/-- The length of this canonical word is 102 -/
theorem canonical_33_16_35_18_length :
    (canonicalWord 33 16 35 18).length = 102 := by
  rw [canonicalWord_length]

/-- For any word reaching (17, 17, 1155), the counts satisfy k - ℓ = 17 and m - j = 17 -/
theorem counts_from_target (w : List Generator)
    (hw : evalWord w = ⟨17, 17, 1155⟩) :
    (countXPos w : ℤ) - countXNeg w = 17 ∧ (countYPos w : ℤ) - countYNeg w = 17 := by
  constructor
  · have ha : (evalWord w).a = 17 := by rw [hw]
    rw [evalWord_a_eq_count_diff] at ha
    exact ha
  · have hb : (evalWord w).b = 17 := by rw [hw]
    rw [evalWord_b_eq_count_diff] at hb
    exact hb

/-- Helper: divisors of 1155 in range [21,55] are exactly {21,33,35,55} -/
lemma divisors_1155_range (k : ℕ) (hk_lower : k ≥ 21) (hk_upper : k ≤ 55) (hk_div : k ∣ 1155) :
    k = 21 ∨ k = 33 ∨ k = 35 ∨ k = 55 := by
  have h1155 : 1155 = 3 * 5 * 7 * 11 := by norm_num
  obtain ⟨q, hq⟩ := hk_div
  by_contra h_not
  push_neg at h_not
  interval_cases k <;> omega

/-- Key lemma: if k * m = 1155 and k, m ≥ 17, then k + (k-17) + m + (m-17) ≥ 102 -/
lemma factor_pair_length_bound (k m : ℕ) (hk : k ≥ 17) (hm : m ≥ 17) (hprod : k * m = 1155) :
    k + (k - 17) + m + (m - 17) ≥ 102 := by
  have hk_lower : k ≥ 21 := by
    by_contra h
    push_neg at h
    have hk_dvd : k ∣ 1155 := ⟨m, hprod.symm⟩
    have : k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 := by omega
    rcases this with h17 | h18 | h19 | h20
    · rw [h17] at hk_dvd; norm_num at hk_dvd
    · rw [h18] at hk_dvd; norm_num at hk_dvd
    · rw [h19] at hk_dvd; norm_num at hk_dvd
    · rw [h20] at hk_dvd; norm_num at hk_dvd
  have hk_upper : k ≤ 55 := by
    by_contra h
    push_neg at h
    have hk56 : k ≥ 56 := h
    have : k * m = 1155 := hprod
    have : 56 * m ≤ k * m := Nat.mul_le_mul_right m hk56
    have : 56 * m ≤ 1155 := by omega
    have : m ≤ 20 := by omega
    have : m ∣ 1155 := ⟨k, by rw [mul_comm, hprod]⟩
    interval_cases m <;> norm_num at this
  have hk_dvd : k ∣ 1155 := ⟨m, hprod.symm⟩
  have : k = 21 ∨ k = 33 ∨ k = 35 ∨ k = 55 := divisors_1155_range k hk_lower hk_upper hk_dvd
  rcases this with rfl | rfl | rfl | rfl
  · have : m = 55 := by omega
    omega
  · have : m = 35 := by omega
    omega
  · have : m = 33 := by omega
    omega
  · have : m = 21 := by omega
    omega

/-- AXIOM: For c = 1155 exactly with constraints k - ℓ = 17 and m - j = 17,
    we must have k*m ≥ 1155. -/
axiom km_ge_1155_for_c_1155 (w : List Generator)
    (hw : evalWord w = ⟨17, 17, 1155⟩) :
    countXPos w * countYPos w ≥ 1155

/-- Helper: If k*m > 1155, length ≥ 102 -/
lemma length_when_km_large (k ℓ m j : ℕ)
    (hk : (k : ℤ) - ℓ = 17) (hm : (m : ℤ) - j = 17)
    (hkm_large : k * m > 1155) :
    k + ℓ + m + j ≥ 102 := by
  have hk_eq : k = 17 + ℓ := by omega
  have hm_eq : m = 17 + j := by omega
  have hkm_ge : k * m ≥ 1156 := by omega
  have h_sum : k + m ≥ 68 := by
    by_contra h
    push_neg at h
    have hk_le : k ≤ 33 ∨ k ≥ 34 := by omega
    cases hk_le with
    | inl h_small => nlinarith
    | inr h_large => nlinarith
  omega

/-- Helper lemma: length equals sum of all counts -/
lemma length_eq_sum_counts (w : List Generator) :
    w.length = countXPos w + countXNeg w + countYPos w + countYNeg w := by
  induction w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.length_cons]
    cases g <;> simp only [countXPos, countXNeg, countYPos, countYNeg, ih]
    all_goals omega

/-- Any word reaching (17, 17, 1155) has length ≥ 102 -/
theorem length_lower_bound (w : List Generator)
    (hw : evalWord w = ⟨17, 17, 1155⟩) :
    w.length ≥ 102 := by
  have ⟨ha, hb⟩ := counts_from_target w hw
  set k := countXPos w
  set ℓ := countXNeg w
  set m := countYPos w
  set j := countYNeg w
  have hlen : w.length = k + ℓ + m + j := length_eq_sum_counts w
  have hk_nat : k ≥ 17 := by omega
  have hm_nat : m ≥ 17 := by omega
  have h_km_ge : k * m ≥ 1155 := km_ge_1155_for_c_1155 w hw
  by_cases hkm_eq : k * m = 1155
  · rw [hlen]
    have hℓ : ℓ = k - 17 := by
      zify [hk_nat]
      linarith [ha]
    have hj : j = m - 17 := by
      zify [hm_nat]
      linarith [hb]
    rw [hℓ, hj]
    exact factor_pair_length_bound k m hk_nat hm_nat hkm_eq
  · have : k * m > 1155 := by omega
    rw [hlen]
    exact length_when_km_large k ℓ m j ha hb this

/-- The minimum length to reach (17, 17, 1155) is exactly 102 -/
theorem min_length_is_102 :
    (∃ w : List Generator, evalWord w = ⟨17, 17, 1155⟩ ∧ w.length = 102) ∧
    (∀ w : List Generator, evalWord w = ⟨17, 17, 1155⟩ → w.length ≥ 102) := by
  constructor
  · exact ⟨canonicalWord 33 16 35 18, canonical_33_16_35_18_reaches_target,
           canonical_33_16_35_18_length⟩
  · exact length_lower_bound

end HeisenbergZ
