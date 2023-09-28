import HTPIDefs
namespace HTPI
set_option pp.funBinderTypes true
set_option linter.unusedVariables false


theorem easy (P Q R : Prop) (h1 : P → Q)
    (h2 : Q → R) (h3 : P) : R :=
    h2 (h1 h3)

theorem two_imp (P Q R : Prop)
    (h1 : P → Q) (h2 : Q → ¬R) : R → ¬P := by
  contrapos
  assume hp
  show ¬R from h2 (h1 hp)
  done



theorem two_imp2 (P Q R : Prop)
    (h1 : P → Q) (h2 : Q → ¬R) : R → ¬P := by

  -- contrapos at h2
-- 
  -- apply h2

  assume hr : R
  contrapos at h2
  contrapos at h1
  show ¬P from h1 (h2 hr)


  -- sorry
  done
