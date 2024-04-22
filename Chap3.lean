import Chap3
namespace HTPI.Exercises
set_option pp.funBinderTypes true
set_option linter.unusedVariables false

theorem Example_3_2_4
    (P Q R : Prop) (h : P → (Q → R)) : ¬R → (P → ¬Q) := by
  assume hnr
  assume hp
  have qr := h hp
  contrapos at qr
  show ¬Q from qr hnr
  done

theorem Example_3_2_4_v2 (P Q R : Prop)
    (h : P → (Q → R)) : ¬R → (P → ¬Q) := by
  assume h2 : ¬R
  assume h3 : P
  by_contra hq
  have hr := (h h3) hq
  show False from h2 hr
  done

theorem Example_3_2_4_v3 (P Q R : Prop)
    (h : P → (Q → R)) : ¬R → (P → ¬Q) := by
  assume h2 : ¬R
  assume h3 : P
  by_contra h4
  contradict h2
  show R from  h h3 h4
  done

theorem Example_3_2_5_simple
    (U : Type)
    (B C : Set U) (a : U)
    (h1 : a ∈ B) (h2 : a ∉ B \ C) : a ∈ C := by
  define at h2
  demorgan at h2
  conditional at h2
  show a ∈ C from h2 h1
  done


theorem Example_3_2_5_simple_my
    (B C : Set Nat) (a : Nat)
    (h1 : a ∈ B) (h2 : a ∉ B \ C) : a ∈ C := by
  define at h2
  demorgan at h2
  show a ∈ C from h2.elim
    (fun h : a ∉ B => absurd h1 h)
    (fun h : a ∈ C => h)
  done

theorem Like_Example_3_2_5
    (U : Type) (A B C : Set U) (a : U)
    (h1 : a ∈ A) (h2 : a ∉ A \ B)
    (h3 : a ∈ B → a ∈ C) : a ∈ C := by

  define at h2
  demorgan at h2
  conditional at h2
  apply h3
  apply h2
  show a ∈ A from h1
  done


example (U : Type) (P Q : Pred U)
    (h1 : ∀ (x : U), P x → ¬Q x)
    (h2 : ∀ (x : U), Q x) :
    ¬∃ (x : U), P x := by
  quant_neg
  fix y
  have hpnq := h1 y

  contrapos at hpnq
  have hq := h2 y

  show ¬P y from hpnq hq
  done

example (U : Type) (A B C : Set U) (h1 : A ⊆ B ∪ C)
    (h2 : ∀ (x : U), x ∈ A → x ∉ B) : A ⊆ C := by

  define
  fix y
  assume ha
  define at h1

  have hnb := h2 y ha
  have hbc := h1 ha
  define at hbc
  conditional at hbc

  show y ∈ C from hbc hnb
  done

example (U : Type) (P Q : Pred U)
    (h1 : ∀ (x : U), ∃ (y : U), P x → ¬ Q y)
    (h2 : ∃ (x : U), ∀ (y : U), P x → Q y) :
    ∃ (x : U), ¬P x := by
  obtain (a : U) (h3 : ∀ (y : U), P a → Q y) from h2

  have h4 : (∃ (y : U), P a → ¬ Q y) := h1 a

  obtain (b : U) (h5 : P a → ¬ Q b) from h4
  have h6 := h3 b

  apply Exists.intro a
  by_contra h7

  show False from absurd (h6 h7) (h5 h7)
  done

theorem Example_3_3_5 (U : Type) (B : Set U)
    (F : Set (Set U)) : ⋃₀ F ⊆ B → F ⊆ 𝒫 B := by
    assume h : ⋃₀F ⊆ B
    define
    fix A : Set U
    assume hf : A ∈ F
    define
    fix y
    assume hya : y ∈ A
    define at h
    apply h
    define
    apply Exists.intro A
    show A ∈ F ∧ y ∈ A from ⟨hf, hya⟩

theorem Like_Example_3_4_1 (U : Type)
    (A B C D : Set U) (h1 : A ⊆ B)
    (h2 : ¬∃ (c : U), c ∈ C ∩ D) :
    A ∩ C ⊆ B \ D := by

  define
  fix x : U
  assume h3 : x ∈ A ∩ C
  define at h3; define
  apply And.intro
  ·
    define at h1
    show x ∈ B from h1 h3.left
    done

  ·
  -- contradict h with h' is shorthand for by_contra h'; contradict h.
    -- by_contra h2
    by_contra h4
    contradict h2
    apply Exists.intro x
    define
    -- contradict h2 with h4
    -- by_contra
    done
  
  done

variable (α : Type) (p q : α → Prop)

theorem Example_3_4_4 : (∀ x, ¬p x) ↔ (¬∃ x, p x) :=
  Iff.intro
  (fun h => by
    by_contra he
    
    obtain a ha from he
    contradict ha
    show ¬p a from h a
    -- contradict 
    -- done
  )
  (fun h => by
    fix a
    by_contra hp
    have hep : (∃ (x: α), p x) := Exists.intro a hp
    show False from h hep
    done
  )


example (U : Type) (P Q : Pred U)
    (h1 : ∀ (x : U), P x ↔ Q x) :
    (∃ (x : U), P x) ↔ ∃ (x : U), Q x := by
    apply Iff.intro
    · -- (→)
      assume h2 : ∃ (x : U), P x
      obtain x' hp from h2
      have hq := (h1 x').ltr hp
      apply Exists.intro x' hq
      done
    · -- (←)
      assume heq
      obtain (u : U) (hq : Q u) from heq
      have h := (h1 u).rtl
      apply Exists.intro u (h hq)
      done


theorem Example_3_4_5 (U : Type)
  (A B C : Set U) : A ∩ (B \ C) = (A ∩ B) \C := by
  apply Set.ext
  fix x : U
  show x ∈ A ∩ (B \ C) ↔ x ∈ (A ∩ B) \ C from
    calc x ∈ A ∩ (B \ C)
      _ ↔ x ∈ A ∧ (x ∈ B ∧ x ∉ C) := Iff.refl _
      _ ↔ (x ∈ A ∧ x ∈ B) ∧ x ∉ C := and_assoc.symm
      _ ↔ x ∈ (A ∩ B) \ C := Iff.refl _
  done


theorem Example_3_5_2
    (U : Type) (A B C : Set U) :
    A \ (B \ C) ⊆ (A \ B) ∪ C := by

    define
    fix x : U
    assume h1
    define
    define at h1

    have ⟨ha, hnbc⟩ := h1
    define at hnbc
    demorgan at hnbc

    show x ∈ A \ B ∨ x ∈ C from (hnbc.elim 
    (fun h => Or.inl ⟨ha, h⟩ )
    (fun h => Or.inr h))


theorem Example_3_6_1__1_2 (U : Type) (P : Pred U)
  (h: ∃ (x:U), P x ∧ ∀ (y:U), (P y → y = x)) :
  ∃ (x:U), ∀ (y:U), (P y ↔ y = x) := by
  obtain x he from h

  apply Exists.intro x

  fix y
  
  apply Iff.intro

  exact he.right y

  assume eq

  rw [eq]
  exact he.left


theorem empty_union {U : Type} (B : Set U) :
    ∅ ∪ B = B := by
    apply Set.ext
    fix x : U
    apply Iff.intro

    assume h
    define at h

    by_cases on h
    . -- x ∈ ∅
      define at h
      exact False.elim h
    . -- x ∈ B
      exact h

    assume h
    exact Or.inr h

#check @or_comm

theorem union_comm {U : Type} (X Y : Set U) :
    X ∪ Y = Y ∪ X := by
  
  apply Set.ext
  fix x : U
  define : x ∈ X ∪ Y
  define : x ∈ Y ∪ X

  exact or_comm
  -- apply or_comm
  -- done

#check Eq.symm

theorem Example_3_6_2 (U : Type) : 
  ∃! (A: Set U), ∀ (B : Set U), 
    A ∪ B = B := by
  exists_unique
  . -- Existence

    apply Exists.intro ∅
    fix B
    apply empty_union B
  
  . -- Uniqueness
    fix A1; fix A2
    assume h1; assume h2
    have u1 := h1 A2
    have u2 := h2 A1

    show A1 = A2 from
        calc A1
        _ = A2 ∪ A1 := u2.symm
        _ = A1 ∪ A2 := union_comm A2 A1
        _ = A2 := u1


-- theorem Example_3_6_3 (x : ℝ)
--   (hn : x ≠ 2) : ∃! (y : ℝ), 2*y / (y+1) = x := by
--     exists_unique

--     . -- Existence

--       have y := x / (2 - x)

--       apply Exists.intro y

--       rw [y = x / (2 - x)]
--       simp
--     . -- Uniqueness

variable (α : Type) (P : α → Prop)

example (x : α) (y : α) (h : P y) (he : x = y) : P x := by
  rw [<- he] at h
  exact h



theorem Example_3_6_4 (U : Type) (A B C : Set U)
    (h1 : ∃ (x : U), x ∈ A ∩ B)
    (h2 : ∃ (x : U), x ∈ A ∩ C)
    (h3 : ∃! (x : U), x ∈ A) :
    ∃ (x : U), x ∈ B ∩ C := by
    obtain xa ha hu from h3
    obtain xb hb from h1
    obtain xc hc from h2
    
    have hac := hc.left
    have hab := hb.left

    have hubc := hu xb xc

    have heq := hubc hab hac

    apply Exists.intro xb

    have h_xb_b := hb.right
    have h_xc_c := hc.right

    define
    rw [<- heq] at h_xc_c

    exact ⟨h_xb_b, h_xc_c⟩




theorem Theorem_3_3_7 :
    ∀ (a b c : Int), a ∣ b → b ∣ c → a ∣ c := by
    fix a; fix b;  fix c;
    assume ha
    assume hb
    define

    obtain i hi from hb
    obtain j hj from ha

    rw [hj] at hi
    apply Exists.intro (j*i)
    rw [mul_assoc] at hi
    exact hi
