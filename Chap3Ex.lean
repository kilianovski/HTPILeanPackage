import Chap3
namespace HTPI.Exercises
set_option pp.funBinderTypes true
set_option linter.unusedVariables false


variable (α : Type) (p q : α → Prop)

example : (¬ ∃ x, p x) → (∀ x, ¬ p x) := by
  intro h
  fix a
  quant_neg at h
  show ¬p a from h a

open Classical

theorem dne {p : Prop} (h : ¬¬p) : p :=
  byCases
    (fun h1 : p => h1)
    (fun h1 : ¬p => absurd h1 h)

theorem exists_neg : (¬ ∃ x, p x) → (∀ x, ¬ p x) := fun h : ( (∃ x, p x) → False ) =>
  fun x => byContradiction (fun hnnpx : ¬¬(p x) => 
    have hpx : p x := dne hnnpx
    have he : (∃ x, p x) := Exists.intro x hpx
    show False from (h he)
  )

/- Sections 3.1 and 3.2 -/
-- 1.
theorem Exercise_3_2_1a (P Q R : Prop)
    (h1 : P → Q) (h2 : Q → R) : P → R := by
  assume hp
  apply h2
  apply h1
  show P from hp
  done



-- 2.
theorem Exercise_3_2_1b (P Q R : Prop)
    (h1 : ¬R → (P → ¬Q)) : P → (Q → R) := by
  assume hp
  assume hq
  contradict hq with hnr
  show ¬Q from h1 hnr hp

-- 3.
theorem Exercise_3_2_2a (P Q R : Prop)
    (h1 : P → Q) (h2 : R → ¬Q) : P → ¬R := by
  
  assume hp
  by_contra hr
  show False from absurd (h1 hp) (h2 hr) 
  done

-- 4.
theorem Exercise_3_2_2b (P Q : Prop)
    (h1 : P) : Q → ¬(Q → ¬P) := by
  assume hq
  by_contra h
  show False from absurd h1 (h hq)
  done


/- Section 3.3 -/
-- 1.
theorem Exercise_3_3_1
    (U : Type) (P Q : Pred U) (h1 : ∃ (x : U), P x → Q x) :
    (∀ (x : U), P x) → ∃ (x : U), Q x := by
  
  assume h
  obtain a ha from h1
  have hq := ha (h a)
  apply Exists.intro a
  show Q a from hq
  done

-- 2.
theorem Exercise_3_3_8 (U : Type) (F : Set (Set U)) (A : Set U)
    (h1 : A ∈ F) : A ⊆ ⋃₀ F := by
    define
    fix y : U
    assume ha : y ∈ A
    define
    apply Exists.intro A
    show A ∈ F ∧ y ∈ A from ⟨h1, ha⟩
-- 3.
theorem Exercise_3_3_9 (U : Type) (F : Set (Set U)) (A : Set U)
    (h1 : A ∈ F) : ⋂₀ F ⊆ A := by
  
  define
  fix y : U
  assume hf
  define at hf
  have ha : A ∈ F → y ∈ A := hf A

  have hya := ha h1
  show y ∈ A from hya


-- 4.
theorem Exercise_3_3_10 (U : Type) (B : Set U) (F : Set (Set U))
    (h1 : ∀ (A : Set U), A ∈ F → B ⊆ A) : B ⊆ ⋂₀ F := by
  
  define

  fix y : U
  assume hb
  define
  fix X : Set U
  assume hXF
  have h2 := h1 X hXF
  define at h2

  have hx : y ∈ X := h2 hb
  show y ∈ X from hx


theorem Exercise_3_3_12 (U : Type)
    (F G : Set (Set U)) : F ⊆ G → ⋃₀ F ⊆ ⋃₀ G := by
  assume h
  define
  fix x
  assume hxf
  define
  define at hxf
  define at h
  obtain (s : Set U) (⟨h2, h3⟩) from hxf
  have hsg : (s ∈ G) := h h2

  apply Exists.intro s
  show s ∈ G ∧ x ∈ s from ⟨hsg, h3⟩
  done

-- 5.
theorem Exercise_3_3_13 (U : Type)
    (F G : Set (Set U)) : F ⊆ G → ⋂₀ G ⊆ ⋂₀ F := by
  
  assume h
  define
  fix x
  assume hxG
  define
  fix s
  assume hsF
  define at hxG
  define at h

  have hxG2 : s ∈ G := h hsF
  have q := hxG s hxG2
  show x ∈ s from q
  done


-- theorem Exercise_3_3_17 (U : Type) (F G : Set (Set U))
--     (h1 : ∀ (A : Set U), A ∈ F → ∀ (B : Set U), B ∈ G → A ⊆ B) :
--     ⋃₀ F ⊆ ⋂₀ G := by
  
--   done

/- Section 3.4 -/
-- 1.
theorem Exercise_3_4_2 (U : Type) (A B C : Set U)
    (h1 : A ⊆ B) (h2 : A ⊆ C) : A ⊆ B ∩ C := by
    define
    fix x : U
    assume ha
    define at h1
    define at h2
    have hb := h1 ha
    have hc := h2 ha
    define
    show x ∈ B ∧ x ∈ C from ⟨hb, hc⟩

-- 2.
theorem Exercise_3_4_4 (U : Type) (A B C : Set U)
    (h1 : A ⊆ B) (h2 : A ⊈ C) : B ⊈ C := by
    define
    by_contra h
    define at h1
    define at h2
    quant_neg at h2
    obtain x hx from h2

    have hnx : x ∈ A → x ∈ C := fun ha => h (h1 ha)
    show False from hx hnx

-- 3.
theorem Exercise_3_3_16 (U : Type) (B : Set U)
    (F : Set (Set U)) : F ⊆ 𝒫 B → ⋃₀ F ⊆ B := by
    assume h
    define
    fix x : U
    assume huf
    define at h
    define at huf
    obtain b hb from huf
    have t := h hb.left
    define at t
    have  p := t hb.right
    show x ∈ B from p
    done
-- 4.
-- theorem Exercise_3_3_17 (U : Type) (F G : Set (Set U))
--     (h1 : ∀ (A : Set U), A ∈ F → ∀ (B : Set U), B ∈ G → A ⊆ B) :
--     ⋃₀ F ⊆ ⋂₀ G :=
--     sorry

  
  -- done

-- -- 5.
-- theorem Exercise_3_4_7 (U : Type) (A B : Set U) :
--     𝒫 (A ∩ B) = 𝒫 A ∩ 𝒫 B := by

--   done

-- -- 6.
-- theorem Exercise_3_4_17 (U : Type) (A : Set U) : A = ⋃₀ (𝒫 A) := by

--   done

-- -- 7.
-- theorem Exercise_3_4_18a (U : Type) (F G : Set (Set U)) :
--     ⋃₀ (F ∩ G) ⊆ (⋃₀ F) ∩ (⋃₀ G) := by
  
--   done

-- -- 8.
-- theorem Exercise_3_4_19 (U : Type) (F G : Set (Set U)) :
--     (⋃₀ F) ∩ (⋃₀ G) ⊆ ⋃₀ (F ∩ G) ↔
--       ∀ (A B : Set U), A ∈ F → B ∈ G → A ∩ B ⊆ ⋃₀ (F ∩ G) := by
  
--   done

/- Section 3.5 -/
-- 1.
theorem Exercise_3_5_2 (U : Type) (A B C : Set U) :
    (A ∪ B) \ C ⊆ A ∪ (B \ C) := by
    define
    fix x : U
    assume h1
    define
    define at h1

    by_cases on h1.left
    . -- Case 1
      apply Or.inl
      show x ∈ A from this
    . -- Case 2
      apply Or.inr
      show x ∈ B \ C from ⟨this, h1.right⟩

-- 2.
theorem Exercise_3_5_5 (U : Type) (A B C : Set U)
    (h1 : A ∩ C ⊆ B ∩ C) (h2 : A ∪ C ⊆ B ∪ C) : A ⊆ B := by
    define
    fix x : U
    assume ha
    define at h2
    define at h1

    have hbc : x ∈ B ∨ x ∈ C := h2 (Or.inl ha)

    by_cases on hbc
    . -- Case 1
      show x ∈ B from hbc
    . -- Case 2
      have ⟨hb, hc⟩ := h1 ⟨ha, hbc⟩
      show x ∈ B from hb

-- 3.
theorem Exercise_3_5_7 (U : Type) (A B C : Set U) :
    A ∪ C ⊆ B ∪ C ↔ A \ C ⊆ B \ C := sorry

-- 4.
theorem Exercise_3_5_8 (U : Type) (A B : Set U) :
    𝒫 A ∪ 𝒫 B ⊆ 𝒫 (A ∪ B) := by
    define
    fix s : Set U
    assume h1
    define
    fix x : U

    assume hs
    define
    define at h1
    -- have ⟨hpa, hpb⟩ := h1

    by_cases on h1

    . 
      define at h1
      apply Or.inl
      show x ∈ A from h1 hs

    . 
      define at h1
      apply Or.inr
      show x ∈ B from h1 hs

#check Iff.refl
#check byCases


-- 5.
theorem Exercise_3_5_17b (U : Type) (F : Set (Set U)) (B : Set U) :
    B ∪ (⋂₀ F) = { x : U | ∀ (A : Set U), A ∈ F → x ∈ B ∪ A } := by
    apply Set.ext
    fix x : U

    show x ∈ B ∪ ⋂₀ F ↔ x ∈ {x : U | ∀ (A : Set U), A ∈ F → x ∈ B ∪ A} from
      calc x ∈ B ∪ ⋂₀ F
        _ ↔ x ∈ B ∨ x ∈ ⋂₀ F := Iff.refl _
        _ ↔ x ∈ B ∨ ∀ (A : Set U), A ∈ F → x ∈ A := Iff.refl _

        _ ↔ ∀ (A : Set U), A ∈ F → (x ∈ B ∨ x ∈ A) := Iff.intro
          (fun h : x ∈ B ∨ ∀ (A : Set U), A ∈ F → x ∈ A =>
            fun A => fun ha => h.elim (fun hb => Or.inl hb) (fun haa => Or.inr (haa A ha))
            )
          (fun h => byCases
            (fun hb : (x ∈ B) => Or.inl hb)
            (fun hnb : ¬(x ∈ B) => Or.inr (fun A => fun ha => 
              have hor := h A ha
              hor.elim (fun hb => absurd hb hnb)
              (fun haa => haa)
            ))
          )





-- 6.
theorem Exercise_3_5_18 (U : Type) (F G H : Set (Set U))
    (h1 : ∀ (A : Set U), A ∈ F → ∀ (B : Set U), B ∈ G → A ∪ B ∈ H) :
    ⋂₀ H ⊆ (⋂₀ F) ∪ (⋂₀ G) := sorry


-- 7.
theorem Exercise_3_5_24a (U : Type) (A B C : Set U) :
    (A ∪ B) △ C ⊆ (A △ C) ∪ (B △ C) := by
    define
    fix s
    assume h
    define
    define at h

    by_cases on h
    . -- Case s ∈ (A ∪ B) \ C 
      define at h
      have hor : s ∈ A ∨ s ∈ B := h.left
      by_cases on hor
      .
        have hs : s ∈ A △ C := Or.inl ⟨hor, h.right⟩
        exact Or.inl hs
      .
        have hs : s ∈ B △ C := Or.inl ⟨hor, h.right⟩
        exact Or.inr hs
    . -- Case s ∈ C \ (A ∪ B)
      define at h
      -- have x :=demorgan h.right
      have hor : ¬ (s ∈ A ∨ s ∈ B) := h.right
      demorgan at hor
      have ⟨hna, hnb⟩ := hor
      have hsd : s ∈ B △ C := Or.inr ⟨h.left, hnb⟩
      exact Or.inr hsd




/- Section 3.6 -/
-- 1.

theorem Exercise_3_4_15 (U : Type) (B : Set U) (F : Set (Set U)) :
    ⋃₀ { X : Set U | ∃ (A : Set U), A ∈ F ∧ X = A \ B }
      ⊆ ⋃₀ (F \ 𝒫 B) := by
    define
    fix x : U
    assume h
    define

    define at h
    obtain S hS from h
    -- obtain
    have ⟨hS, hxS⟩ := hS
    define at hS
    obtain A hA from hS
    have ⟨hA, hSB⟩ := hA

    apply Exists.intro A

    rw [hSB] at hxS
    define at hxS

    have hAnPB : ¬ A ∈ 𝒫 B := by
      define
      quant_neg
      push_neg
      apply Exists.intro x
      exact hxS
    
    apply And.intro
    define

    show A∈F ∧ ¬A ∈ 𝒫 B from ⟨hA, hAnPB⟩

    exact hxS.left



-- theorem Exercise_3_4_15 (U : Type) (B : Set U) (F : Set (Set U)) :
--     ⋃₀ { X : Set U | ∃ (A : Set U), A ∈ F ∧ X = A \ B }
--       ⊆ ⋃₀ (F \ 𝒫 B) := by
    
--     define

--     fix x : U
--     assume h

--     define at h
--     obtain s hs from h
--     define

--     have ⟨hs, hxs⟩ := hs
--     define at hs
--     obtain A ha from hs
--     rw [ha.right] at hxs

--     define at hxs
--     have my_set : Set U := { x } -- This should be the way..

--     have hxx : x ∈ my_set := 

--     have hxab : x ∈ A \ B :=
--       calc x ∈ s
--         _ = 



    -- define at hs
    -- Looks like dead end:

    -- apply Exists.intro s

    -- apply And.intro

    -- . -- Case s ∈ (F \ 𝒫 B)
    --   have hs := hs.left
  
    --   define at hs

    --   obtain A ha from hs

    --   have hsa := ha.right

    --   define
    --   apply And.intro

    --   . -- Case s ∈ F

      

    --   . -- Case 


    -- . -- case x ∈ s
    --   exact hs.right





-- 2.
theorem Exercise_3_5_9 (U : Type) (A B : Set U)
    (h1 : 𝒫 (A ∪ B) = 𝒫 A ∪ 𝒫 B) : A ⊆ B ∨ B ⊆ A := by
  --Hint:  Start like this:
  have h2 : A ∪ B ∈ 𝒫 (A ∪ B) := sorry
  done

-- 3.
theorem Exercise_3_6_6b (U : Type) :
    ∃! (A : Set U), ∀ (B : Set U), A ∪ B = A := sorry

-- 4.
theorem Exercise_3_6_7b (U : Type) :
    ∃! (A : Set U), ∀ (B : Set U), A ∩ B = A := sorry

-- 5.
theorem Exercise_3_6_8a (U : Type) : ∀ (A : Set U),
    ∃! (B : Set U), ∀ (C : Set U), C \ A = C ∩ B := sorry

-- 6.
theorem Exercise_3_6_10 (U : Type) (A : Set U)
    (h1 : ∀ (F : Set (Set U)), ⋃₀ F = A → A ∈ F) :
    ∃! (x : U), x ∈ A := by
  --Hint:  Start like this:
  set F0 : Set (Set U) := { X : Set U | X ⊆ A ∧ ∃! (x : U), x ∈ X }
  --Now F0 is in the tactic state, with the definition above
  have h2 : ⋃₀ F0 = A := sorry
  
  done

/- Section 3.7 -/
-- 1.
theorem Exercise_3_3_18a (a b c : Int)
    (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ (b + c) := sorry

-- 2.
theorem Exercise_3_4_6 (U : Type) (A B C : Set U) :
    A \ (B ∩ C) = (A \ B) ∪ (A \ C) := by
  apply Set.ext
  fix x : U
  show x ∈ A \ (B ∩ C) ↔ x ∈ A \ B ∪ A \ C from
    calc x ∈ A \ (B ∩ C)
      _ ↔ x ∈ A ∧ ¬(x ∈ B ∧ x ∈ C) := sorry
      _ ↔ x ∈ A ∧ (¬x ∈ B ∨ ¬x ∈ C) := sorry  
      _ ↔ (x ∈ A ∧ ¬x ∈ B) ∨ (x ∈ A ∧ ¬x ∈ C) := sorry
      _ ↔ x ∈ (A \ B) ∪ (A \ C) := sorry
  done

-- 3.
theorem Exercise_3_4_10 (x y : Int)
    (h1 : odd x) (h2 : odd y) : even (x - y) := sorry

-- 4.
theorem Exercise_3_4_27a :
    ∀ (n : Int), 15 ∣ n ↔ 3 ∣ n ∧ 5 ∣ n := sorry

-- 5.
theorem Like_Exercise_3_7_5 (U : Type) (F : Set (Set U))
    (h1 : 𝒫 (⋃₀ F) ⊆ ⋃₀ { 𝒫 A | A ∈ F }) :
    ∃ (A : Set U), A ∈ F ∧ ∀ (B : Set U), B ∈ F → B ⊆ A := sorry
