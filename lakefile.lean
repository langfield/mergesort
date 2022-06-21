import Lake
open Lake DSL

package mergesort {
  dependencies := #[{
    name := `mathlib
    src := Source.git "https://github.com/leanprover-community/mathlib4.git" "4df5616da077213c63c85d702f7b78e268792636"
  }]
}
