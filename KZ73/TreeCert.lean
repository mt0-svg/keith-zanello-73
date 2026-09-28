import KZ73.Tree

/-!
# Kernel certificate of the partition at level 14

One declaration per odd residue `τ < 128`, each checking the `128` balls `B(τ + 128 s, 14)` and
the deeper balls below them, by `decide +kernel` (kernel evaluation with GMP arithmetic, no
`native_decide`). Generated text: one line per residue.
-/

namespace KeithZanello

theorem sweepFrom_1 : sweepFrom 1 = true := by decide +kernel
theorem sweepFrom_3 : sweepFrom 3 = true := by decide +kernel
theorem sweepFrom_5 : sweepFrom 5 = true := by decide +kernel
theorem sweepFrom_7 : sweepFrom 7 = true := by decide +kernel
theorem sweepFrom_9 : sweepFrom 9 = true := by decide +kernel
theorem sweepFrom_11 : sweepFrom 11 = true := by decide +kernel
theorem sweepFrom_13 : sweepFrom 13 = true := by decide +kernel
theorem sweepFrom_15 : sweepFrom 15 = true := by decide +kernel
theorem sweepFrom_17 : sweepFrom 17 = true := by decide +kernel
theorem sweepFrom_19 : sweepFrom 19 = true := by decide +kernel
theorem sweepFrom_21 : sweepFrom 21 = true := by decide +kernel
theorem sweepFrom_23 : sweepFrom 23 = true := by decide +kernel
theorem sweepFrom_25 : sweepFrom 25 = true := by decide +kernel
theorem sweepFrom_27 : sweepFrom 27 = true := by decide +kernel
theorem sweepFrom_29 : sweepFrom 29 = true := by decide +kernel
theorem sweepFrom_31 : sweepFrom 31 = true := by decide +kernel
theorem sweepFrom_33 : sweepFrom 33 = true := by decide +kernel
theorem sweepFrom_35 : sweepFrom 35 = true := by decide +kernel
theorem sweepFrom_37 : sweepFrom 37 = true := by decide +kernel
theorem sweepFrom_39 : sweepFrom 39 = true := by decide +kernel
theorem sweepFrom_41 : sweepFrom 41 = true := by decide +kernel
theorem sweepFrom_43 : sweepFrom 43 = true := by decide +kernel
theorem sweepFrom_45 : sweepFrom 45 = true := by decide +kernel
theorem sweepFrom_47 : sweepFrom 47 = true := by decide +kernel
theorem sweepFrom_49 : sweepFrom 49 = true := by decide +kernel
theorem sweepFrom_51 : sweepFrom 51 = true := by decide +kernel
theorem sweepFrom_53 : sweepFrom 53 = true := by decide +kernel
theorem sweepFrom_55 : sweepFrom 55 = true := by decide +kernel
theorem sweepFrom_57 : sweepFrom 57 = true := by decide +kernel
theorem sweepFrom_59 : sweepFrom 59 = true := by decide +kernel
theorem sweepFrom_61 : sweepFrom 61 = true := by decide +kernel
theorem sweepFrom_63 : sweepFrom 63 = true := by decide +kernel
theorem sweepFrom_65 : sweepFrom 65 = true := by decide +kernel
theorem sweepFrom_67 : sweepFrom 67 = true := by decide +kernel
theorem sweepFrom_69 : sweepFrom 69 = true := by decide +kernel
theorem sweepFrom_71 : sweepFrom 71 = true := by decide +kernel
theorem sweepFrom_73 : sweepFrom 73 = true := by decide +kernel
theorem sweepFrom_75 : sweepFrom 75 = true := by decide +kernel
theorem sweepFrom_77 : sweepFrom 77 = true := by decide +kernel
theorem sweepFrom_79 : sweepFrom 79 = true := by decide +kernel
theorem sweepFrom_81 : sweepFrom 81 = true := by decide +kernel
theorem sweepFrom_83 : sweepFrom 83 = true := by decide +kernel
theorem sweepFrom_85 : sweepFrom 85 = true := by decide +kernel
theorem sweepFrom_87 : sweepFrom 87 = true := by decide +kernel
theorem sweepFrom_89 : sweepFrom 89 = true := by decide +kernel
theorem sweepFrom_91 : sweepFrom 91 = true := by decide +kernel
theorem sweepFrom_93 : sweepFrom 93 = true := by decide +kernel
theorem sweepFrom_95 : sweepFrom 95 = true := by decide +kernel
theorem sweepFrom_97 : sweepFrom 97 = true := by decide +kernel
theorem sweepFrom_99 : sweepFrom 99 = true := by decide +kernel
theorem sweepFrom_101 : sweepFrom 101 = true := by decide +kernel
theorem sweepFrom_103 : sweepFrom 103 = true := by decide +kernel
theorem sweepFrom_105 : sweepFrom 105 = true := by decide +kernel
theorem sweepFrom_107 : sweepFrom 107 = true := by decide +kernel
theorem sweepFrom_109 : sweepFrom 109 = true := by decide +kernel
theorem sweepFrom_111 : sweepFrom 111 = true := by decide +kernel
theorem sweepFrom_113 : sweepFrom 113 = true := by decide +kernel
theorem sweepFrom_115 : sweepFrom 115 = true := by decide +kernel
theorem sweepFrom_117 : sweepFrom 117 = true := by decide +kernel
theorem sweepFrom_119 : sweepFrom 119 = true := by decide +kernel
theorem sweepFrom_121 : sweepFrom 121 = true := by decide +kernel
theorem sweepFrom_123 : sweepFrom 123 = true := by decide +kernel
theorem sweepFrom_125 : sweepFrom 125 = true := by decide +kernel
theorem sweepFrom_127 : sweepFrom 127 = true := by decide +kernel

theorem sweepFrom_all : ∀ τ < 128, τ % 2 = 1 → sweepFrom τ = true := by
  have := sweepFrom_1
  have := sweepFrom_3
  have := sweepFrom_5
  have := sweepFrom_7
  have := sweepFrom_9
  have := sweepFrom_11
  have := sweepFrom_13
  have := sweepFrom_15
  have := sweepFrom_17
  have := sweepFrom_19
  have := sweepFrom_21
  have := sweepFrom_23
  have := sweepFrom_25
  have := sweepFrom_27
  have := sweepFrom_29
  have := sweepFrom_31
  have := sweepFrom_33
  have := sweepFrom_35
  have := sweepFrom_37
  have := sweepFrom_39
  have := sweepFrom_41
  have := sweepFrom_43
  have := sweepFrom_45
  have := sweepFrom_47
  have := sweepFrom_49
  have := sweepFrom_51
  have := sweepFrom_53
  have := sweepFrom_55
  have := sweepFrom_57
  have := sweepFrom_59
  have := sweepFrom_61
  have := sweepFrom_63
  have := sweepFrom_65
  have := sweepFrom_67
  have := sweepFrom_69
  have := sweepFrom_71
  have := sweepFrom_73
  have := sweepFrom_75
  have := sweepFrom_77
  have := sweepFrom_79
  have := sweepFrom_81
  have := sweepFrom_83
  have := sweepFrom_85
  have := sweepFrom_87
  have := sweepFrom_89
  have := sweepFrom_91
  have := sweepFrom_93
  have := sweepFrom_95
  have := sweepFrom_97
  have := sweepFrom_99
  have := sweepFrom_101
  have := sweepFrom_103
  have := sweepFrom_105
  have := sweepFrom_107
  have := sweepFrom_109
  have := sweepFrom_111
  have := sweepFrom_113
  have := sweepFrom_115
  have := sweepFrom_117
  have := sweepFrom_119
  have := sweepFrom_121
  have := sweepFrom_123
  have := sweepFrom_125
  have := sweepFrom_127
  intro τ hτ hodd
  interval_cases τ <;> omega

/-- **The paper's Proposition 17 at `p = 73`**: under condition (S) for the balls around `1` and `3`,
every odd `T` outside `E73` is closed, provided condition (G) holds for the centre `t` with
`T ≡ t (mod 2^14)`, if there is one. -/
theorem closed_of_not_mem_E73 (hS1 : CondS1) (hS3 : CondS3) {T : ℕ} (hT : T % 2 = 1)
    (hTE : T ∉ E73) (hC : CentreHyp T) : Closed (fbar ^ T) := by
  have h : GoodClass 1 1 := goodClass_of_forall (by norm_num) fun τ hτ hmod ↦
    goodClass_of_sweepFrom hS1 hS3 hτ (sweepFrom_all τ hτ (by simpa using hmod))
  exact h T (by simpa using hT) hTE hC

end KeithZanello
