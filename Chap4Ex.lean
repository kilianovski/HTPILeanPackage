import Chap4
-- import Mathlib
namespace HTPI.Exercises
set_option pp.funBinderTypes true
set_option linter.unusedVariables false







/- Section 4.2 -/

theorem Theorem_4_2_5_4 {A B C D : Type}
    (R : Set (A × B)) (S : Set (B × C)) (T : Set (C × D)) :
    comp T (comp S R) = comp (comp T S) R := by
    apply Set.ext
    fix (a, d) : A × D

    apply Iff.intro
    · -- (→)

        assume h -- (a, d) ∈ comp T (comp S R)
        define at h -- ∃ c, (a,c) ∈ comp S R ∧ (c,d) ∈ T
        obtain c hc from h
        have ⟨hsr, ht⟩ := hc
        define at hsr
        obtain b hb from hsr

        define
        apply Exists.intro b

        apply And.intro hb.left
        define
        apply Exists.intro c
        apply And.intro hb.right
        exact ht

    -- rfl
    sorry

#check inv


theorem Theorem_4_2_5_5 {A B C : Type}
    (R : Set (A × B)) (S : Set (B × C)) :
    inv (comp S R) = comp (inv R) (inv S) := by

    apply Set.ext
    fix (c, a) : (C × A)

    apply Iff.intro
    · -- (→)
        assume h1

        define at h1
        obtain b (⟨hbR,hbS⟩) from h1

        -- rw [inv, inv]

        define

        apply Exists.intro b
        rewrite [inv_def, inv_def]
        show (b, c) ∈ S ∧ (a, b) ∈ R from ⟨hbS, hbR⟩
    . -- (<-)
        assume h1
        define
        define at h1
        obtain b (⟨hbS,hbR⟩) from h1
        apply Exists.intro b
        rw [inv_def] at hbS
        rw [inv_def] at hbR
        show (a, b) ∈ R ∧ (b, c) ∈ S from ⟨hbR, hbS⟩
    done


theorem their_Theorem_4_2_5_5 {A B C : Type}
    (R : Set (A × B)) (S : Set (B × C)) :
    inv (comp S R) = comp (inv R) (inv S) := by

    apply Set.ext
    fix (c, a) : (C × A)

    apply Iff.intro
    · -- (→)
        assume h1
        define at h1
        obtain b h2 from h1

        define
        apply Exists.intro b
        apply And.intro
        . -- (c, b) ∈ inv S
            define
            show (b, c) ∈ S from h2.right

        . --
            define
            show (a, b) ∈ R from h2.left
    sorry





-- 1.
theorem Exercise_4_2_9a {A B C : Type} (R : Set (A × B))
    (S : Set (B × C)) : Dom (comp S R) ⊆ Dom R := by
    define
    fix a
    assume h -- a ∈ Dom (comp S R)
    define
    define at h
    obtain c hc from h
    define at hc
    obtain b hb from hc
    apply Exists.intro b
    show (a, b) ∈ R from hb.left


lemma empty_contains_something {A : Type} (h: ∃ x : A, x ∈ ∅) : False := by
    obtain x hx from h
    define at hx
    exact hx


-- theorem Exercise_4_2_9a_my {A B C : Type} (R : Set (A × B))
--     (S : Set (B × C)) : Dom (comp S R) ≠ Dom R := by
--     define
--     by_contra h


--     have myS : Set (Nat × Nat) := ∅
--     have myR : Set (Nat × Nat) := {(1,2)}


--     have x := Dom myR
--     have c := comp myS myR


--     rw [Dom, Dom] at h


--     have t := h.left


-- 2.
theorem Exercise_4_2_9b {A B C : Type} (R : Set (A × B))
    (S : Set (B × C)) : Ran R ⊆ Dom S → Dom (comp S R) = Dom R := by
    assume h
    define at h
    apply Set.ext
    fix a
    apply Iff.intro
    . -- -->
        assume h2
        define at h2
        obtain c hc from h2
        define
        define at hc
        obtain b hb from hc
        apply Exists.intro b
        show (a,b) ∈ R from hb.left

    . -- <--
        assume h2
        define
        define at h2
        obtain b hb from h2
        have hr : b ∈ Ran R := by
            define
            apply Exists.intro a
            exact hb

        have h3 := h hr
        define at h3

        obtain c hc from h3

        apply Exists.intro c
        define
        apply Exists.intro b
        show (a, b) ∈ R ∧ (b, c) ∈ S from ⟨hb, hc⟩

        -- appl



-- 3.
--Fill in the blank to get a correct theorem and then prove the theorem
theorem Exercise_4_2_9c {A B C : Type} (R : Set (A × B))
    (S : Set (B × C)) : ___ → Ran (comp S R) = Ran S := sorry

-- 4.
theorem Exercise_4_2_12a {A B C : Type}
    (R : Set (A × B)) (S T : Set (B × C)) :
    (comp S R) \ (comp T R) ⊆ comp (S \ T) R := by
    define
    fix (a, c)
    assume h
    define at h
    define
    have ⟨h1, h2⟩ := h
    define at h1
    obtain b hb from h1
    apply Exists.intro b
    apply And.intro hb.left
    define
    apply And.intro hb.right

    define at h2
    quant_neg at h2
    have h3 := h2 b
    demorgan at h3

    show ¬(b, c) ∈ T from h3.elim
        (fun h : ¬(a,b) ∈ R => absurd hb.left h)
        (fun h : ¬(b,c) ∈ T  => h)



-- 5.
--You won't be able to complete this proof
theorem Exercise_4_2_12b {A B C : Type}
    (R : Set (A × B)) (S T : Set (B × C)) :
    comp (S \ T) R ⊆ (comp S R) \ (comp T R) := sorry

-- 6.
--You might not be able to complete this proof
theorem Exercise_4_2_14c {A B C : Type}
    (R : Set (A × B)) (S T : Set (B × C)) :
    comp (S ∩ T) R = (comp S R) ∩ (comp T R) := sorry

-- 7.
--You might not be able to complete this proof
theorem Exercise_4_2_14d {A B C : Type}
    (R : Set (A × B)) (S T : Set (B × C)) :
    comp (S ∪ T) R = (comp S R) ∪ (comp T R) := sorry

/- Section 4.3 -/
-- 1.
example :
    elementhood Int 6 { n : Int | ∃ (k : Int), n = 2 * k } := sorry

-- 2.
theorem Theorem_4_3_4_1 {A : Type} (R : BinRel A) :
    reflexive R ↔ { (x, y) : A × A | x = y } ⊆ extension R := sorry

-- 3.
theorem Theorem_4_3_4_3 {A : Type} (R : BinRel A) :
    transitive R ↔
      comp (extension R) (extension R) ⊆ extension R := sorry

-- 4.
theorem Exercise_4_3_12a {A : Type} (R : BinRel A) (h1 : reflexive R) :
    reflexive (RelFromExt (inv (extension R))) := sorry

-- 5.
theorem Exercise_4_3_12c {A : Type} (R : BinRel A) (h1 : transitive R) :
    transitive (RelFromExt (inv (extension R))) := sorry

-- 6.
theorem Exercise_4_3_18 {A : Type}
    (R S : BinRel A) (h1 : transitive R) (h2 : transitive S)
    (h3 : comp (extension S) (extension R) ⊆
      comp (extension R) (extension S)) :
    transitive (RelFromExt (comp (extension R) (extension S))) := sorry

-- 7.
theorem Exercise_4_3_20 {A : Type} (R : BinRel A) (S : BinRel (Set A))
    (h : ∀ (X Y : Set A), S X Y ↔ X ≠ ∅ ∧ Y ≠ ∅ ∧
    ∀ (x y : A), x ∈ X → y ∈ Y → R x y) :
    transitive R → transitive S := sorry

-- 8.
--You might not be able to complete this proof
theorem Exercise_4_3_13b {A : Type}
    (R1 R2 : BinRel A) (h1 : symmetric R1) (h2 : symmetric R2) :
    symmetric (RelFromExt ((extension R1) ∪ (extension R2))) := sorry

-- 9.
--You might not be able to complete this proof
theorem Exercise_4_3_13c {A : Type}
    (R1 R2 : BinRel A) (h1 : transitive R1) (h2 : transitive R2) :
    transitive (RelFromExt ((extension R1) ∪ (extension R2))) := sorry

-- 10.
--You might not be able to complete this proof
theorem Exercise_4_3_19 {A : Type} (R : BinRel A) (S : BinRel (Set A))
    (h : ∀ (X Y : Set A), S X Y ↔ ∃ (x y : A), x ∈ X ∧ y ∈ Y ∧ R x y) :
    transitive R → transitive S := sorry

/- Section 4.4 -/
-- 1.
theorem Example_4_4_3_1 {A : Type} : partial_order (sub A) := sorry

-- 2.
theorem Theorem_4_4_6_1 {A : Type} (R : BinRel A) (B : Set A) (b : A)
    (h1 : partial_order R) (h2 : smallestElt R b B) :
    ∀ (c : A), smallestElt R c B → b = c := sorry

-- 3.
--If F is a set of sets, then ⋃₀ F is the lub of F in the subset ordering
theorem Theorem_4_4_11 {A : Type} (F : Set (Set A)) :
    lub (sub A) (⋃₀ F) F := sorry

-- 4.
theorem Exercise_4_4_8 {A B : Type} (R : BinRel A) (S : BinRel B)
    (T : BinRel (A × B)) (h1 : partial_order R) (h2 : partial_order S)
    (h3 : ∀ (a a' : A) (b b' : B),
      T (a, b) (a', b') ↔ R a a' ∧ S b b') :
    partial_order T := sorry

-- 5.
theorem Exercise_4_4_9_part {A B : Type} (R : BinRel A) (S : BinRel B)
    (L : BinRel (A × B)) (h1 : total_order R) (h2 : total_order S)
    (h3 : ∀ (a a' : A) (b b' : B),
      L (a, b) (a', b') ↔ R a a' ∧ (a = a' → S b b')) :
    ∀ (a a' : A) (b b' : B),
      L (a, b) (a', b') ∨ L (a', b') (a, b) := sorry

-- 6.
theorem Exercise_4_4_15a {A : Type}
    (R1 R2 : BinRel A) (B : Set A) (b : A)
    (h1 : partial_order R1) (h2 : partial_order R2)
    (h3 : extension R1 ⊆ extension R2) :
    smallestElt R1 b B → smallestElt R2 b B := sorry

-- 7.
theorem Exercise_4_4_15b {A : Type}
    (R1 R2 : BinRel A) (B : Set A) (b : A)
    (h1 : partial_order R1) (h2 : partial_order R2)
    (h3 : extension R1 ⊆ extension R2) :
    minimalElt R2 b B → minimalElt R1 b B := sorry

-- 8.
theorem Exercise_4_4_18a {A : Type}
    (R : BinRel A) (B1 B2 : Set A) (h1 : partial_order R)
    (h2 : ∀ x ∈ B1, ∃ y ∈ B2, R x y) (h3 : ∀ x ∈ B2, ∃ y ∈ B1, R x y) :
    ∀ (x : A), upperBd R x B1 ↔ upperBd R x B2 := sorry

-- 9.
theorem Exercise_4_4_22 {A : Type}
    (R : BinRel A) (B1 B2 : Set A) (x1 x2 : A)
    (h1 : partial_order R) (h2 : lub R x1 B1) (h3 : lub R x2 B2) :
    B1 ⊆ B2 → R x1 x2 := sorry

-- 10.
theorem Exercise_4_4_24 {A : Type} (R : Set (A × A)) :
    smallestElt (sub (A × A)) (R ∪ (inv R))
    { T : Set (A × A) | R ⊆ T ∧ symmetric (RelFromExt T) } := sorry

/- Section 4.5 -/
-- 1.
lemma overlap_implies_equal {A : Type}
    (F : Set (Set A)) (h : partition F) :
    ∀ X ∈ F, ∀ Y ∈ F, ∀ (x : A), x ∈ X → x ∈ Y → X = Y := sorry

-- 2.
lemma Lemma_4_5_7_ref {A : Type} (F : Set (Set A)) (h : partition F) :
    reflexive (EqRelFromPart F) := sorry

-- 3.
lemma Lemma_4_5_7_symm {A : Type} (F : Set (Set A)) (h : partition F) :
    symmetric (EqRelFromPart F) := sorry

-- 4.
lemma Lemma_4_5_7_trans {A : Type} (F : Set (Set A)) (h : partition F) :
    transitive (EqRelFromPart F) := sorry

-- 5.
lemma Lemma_4_5_8 {A : Type} (F : Set (Set A)) (h : partition F) :
    ∀ X ∈ F, ∀ x ∈ X, equivClass (EqRelFromPart F) x = X := sorry

-- 6.
lemma elt_mod_equiv_class_of_elt
    {A : Type} (R : BinRel A) (h : equiv_rel R) :
    ∀ X ∈ mod A R, ∀ x ∈ X, equivClass R x = X := sorry

-- Definitions for next three exercises:
def dot {A : Type} (F G : Set (Set A)) : Set (Set A) :=
    { Z : Set A | ¬empty Z ∧ ∃ X ∈ F, ∃ Y ∈ G, Z = X ∩ Y }

def conj {A : Type} (R S : BinRel A) (x y : A) : Prop :=
    R x y ∧ S x y

-- 7.
theorem Exercise_4_5_20a {A : Type} (R S : BinRel A)
    (h1 : equiv_rel R) (h2 : equiv_rel S) :
    equiv_rel (conj R S) := sorry

-- 8.
theorem Exercise_4_5_20b {A : Type} (R S : BinRel A)
    (h1 : equiv_rel R) (h2 : equiv_rel S) :
    ∀ (x : A), equivClass (conj R S) x =
      equivClass R x ∩ equivClass S x := sorry

-- 9.
theorem Exercise_4_5_20c {A : Type} (R S : BinRel A)
    (h1 : equiv_rel R) (h2 : equiv_rel S) :
    mod A (conj R S) = dot (mod A R) (mod A S) := sorry

-- 10.
def equiv_mod (m x y : Int) : Prop := m ∣ (x - y)

theorem Theorem_4_5_10 : ∀ (m : Int), equiv_rel (equiv_mod m) := sorry
