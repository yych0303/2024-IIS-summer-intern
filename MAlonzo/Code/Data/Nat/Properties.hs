{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Data.Nat.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.Base
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp
import qualified MAlonzo.Code.Algebra.Definitions.RawMagma
import qualified MAlonzo.Code.Algebra.Lattice.Bundles
import qualified MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp
import qualified MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp
import qualified MAlonzo.Code.Algebra.Lattice.Structures
import qualified MAlonzo.Code.Algebra.Morphism
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Function.Metric.Nat.Bundles
import qualified MAlonzo.Code.Function.Metric.Structures
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Consequences
import qualified MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd
import qualified MAlonzo.Code.Relation.Binary.Definitions
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Algebra
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Binary.Structures.Biased
import qualified MAlonzo.Code.Relation.Nullary.Decidable
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.Nat.Properties._._DistributesOver_
d__DistributesOver__10 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d__DistributesOver__10 = erased
-- Data.Nat.Properties._._DistributesOverʳ_
d__DistributesOver'691'__12 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d__DistributesOver'691'__12 = erased
-- Data.Nat.Properties._._DistributesOverˡ_
d__DistributesOver'737'__14 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) -> ()
d__DistributesOver'737'__14 = erased
-- Data.Nat.Properties._.Associative
d_Associative_30 :: (Integer -> Integer -> Integer) -> ()
d_Associative_30 = erased
-- Data.Nat.Properties._.Commutative
d_Commutative_32 :: (Integer -> Integer -> Integer) -> ()
d_Commutative_32 = erased
-- Data.Nat.Properties._.Identity
d_Identity_48 :: Integer -> (Integer -> Integer -> Integer) -> ()
d_Identity_48 = erased
-- Data.Nat.Properties._.LeftIdentity
d_LeftIdentity_72 ::
  Integer -> (Integer -> Integer -> Integer) -> ()
d_LeftIdentity_72 = erased
-- Data.Nat.Properties._.LeftZero
d_LeftZero_80 :: Integer -> (Integer -> Integer -> Integer) -> ()
d_LeftZero_80 = erased
-- Data.Nat.Properties._.RightIdentity
d_RightIdentity_100 ::
  Integer -> (Integer -> Integer -> Integer) -> ()
d_RightIdentity_100 = erased
-- Data.Nat.Properties._.RightZero
d_RightZero_108 :: Integer -> (Integer -> Integer -> Integer) -> ()
d_RightZero_108 = erased
-- Data.Nat.Properties._.Zero
d_Zero_128 :: Integer -> (Integer -> Integer -> Integer) -> ()
d_Zero_128 = erased
-- Data.Nat.Properties._.IsAbelianGroup
d_IsAbelianGroup_132 a0 a1 a2 = ()
-- Data.Nat.Properties._.IsAlternativeMagma
d_IsAlternativeMagma_134 a0 = ()
-- Data.Nat.Properties._.IsBand
d_IsBand_136 a0 = ()
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring
d_IsCancellativeCommutativeSemiring_138 a0 a1 a2 a3 = ()
-- Data.Nat.Properties._.IsCommutativeBand
d_IsCommutativeBand_140 a0 = ()
-- Data.Nat.Properties._.IsCommutativeMagma
d_IsCommutativeMagma_142 a0 = ()
-- Data.Nat.Properties._.IsCommutativeMonoid
d_IsCommutativeMonoid_144 a0 a1 = ()
-- Data.Nat.Properties._.IsCommutativeRing
d_IsCommutativeRing_146 a0 a1 a2 a3 a4 = ()
-- Data.Nat.Properties._.IsCommutativeSemigroup
d_IsCommutativeSemigroup_148 a0 = ()
-- Data.Nat.Properties._.IsCommutativeSemiring
d_IsCommutativeSemiring_150 a0 a1 a2 a3 = ()
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne
d_IsCommutativeSemiringWithoutOne_152 a0 a1 a2 = ()
-- Data.Nat.Properties._.IsFlexibleMagma
d_IsFlexibleMagma_154 a0 = ()
-- Data.Nat.Properties._.IsGroup
d_IsGroup_156 a0 a1 a2 = ()
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid
d_IsIdempotentCommutativeMonoid_158 a0 a1 = ()
-- Data.Nat.Properties._.IsIdempotentMagma
d_IsIdempotentMagma_160 a0 = ()
-- Data.Nat.Properties._.IsIdempotentMonoid
d_IsIdempotentMonoid_162 a0 a1 = ()
-- Data.Nat.Properties._.IsIdempotentSemiring
d_IsIdempotentSemiring_164 a0 a1 a2 a3 = ()
-- Data.Nat.Properties._.IsInvertibleMagma
d_IsInvertibleMagma_166 a0 a1 a2 = ()
-- Data.Nat.Properties._.IsInvertibleUnitalMagma
d_IsInvertibleUnitalMagma_168 a0 a1 a2 = ()
-- Data.Nat.Properties._.IsKleeneAlgebra
d_IsKleeneAlgebra_170 a0 a1 a2 a3 a4 = ()
-- Data.Nat.Properties._.IsLeftBolLoop
d_IsLeftBolLoop_172 a0 a1 a2 a3 = ()
-- Data.Nat.Properties._.IsLoop
d_IsLoop_174 a0 a1 a2 a3 = ()
-- Data.Nat.Properties._.IsMagma
d_IsMagma_176 a0 = ()
-- Data.Nat.Properties._.IsMedialMagma
d_IsMedialMagma_178 a0 = ()
-- Data.Nat.Properties._.IsMiddleBolLoop
d_IsMiddleBolLoop_180 a0 a1 a2 a3 = ()
-- Data.Nat.Properties._.IsMonoid
d_IsMonoid_182 a0 a1 = ()
-- Data.Nat.Properties._.IsMoufangLoop
d_IsMoufangLoop_184 a0 a1 a2 a3 = ()
-- Data.Nat.Properties._.IsNearSemiring
d_IsNearSemiring_186 a0 a1 a2 = ()
-- Data.Nat.Properties._.IsNearring
d_IsNearring_188 a0 a1 a2 a3 a4 = ()
-- Data.Nat.Properties._.IsNonAssociativeRing
d_IsNonAssociativeRing_190 a0 a1 a2 a3 a4 = ()
-- Data.Nat.Properties._.IsQuasigroup
d_IsQuasigroup_192 a0 a1 a2 = ()
-- Data.Nat.Properties._.IsQuasiring
d_IsQuasiring_194 a0 a1 a2 a3 = ()
-- Data.Nat.Properties._.IsRightBolLoop
d_IsRightBolLoop_196 a0 a1 a2 a3 = ()
-- Data.Nat.Properties._.IsRing
d_IsRing_198 a0 a1 a2 a3 a4 = ()
-- Data.Nat.Properties._.IsRingWithoutOne
d_IsRingWithoutOne_200 a0 a1 a2 a3 = ()
-- Data.Nat.Properties._.IsSelectiveMagma
d_IsSelectiveMagma_202 a0 = ()
-- Data.Nat.Properties._.IsSemigroup
d_IsSemigroup_204 a0 = ()
-- Data.Nat.Properties._.IsSemimedialMagma
d_IsSemimedialMagma_206 a0 = ()
-- Data.Nat.Properties._.IsSemiring
d_IsSemiring_208 a0 a1 a2 a3 = ()
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero
d_IsSemiringWithoutAnnihilatingZero_210 a0 a1 a2 a3 = ()
-- Data.Nat.Properties._.IsSemiringWithoutOne
d_IsSemiringWithoutOne_212 a0 a1 a2 = ()
-- Data.Nat.Properties._.IsUnitalMagma
d_IsUnitalMagma_216 a0 a1 = ()
-- Data.Nat.Properties._.IsAbelianGroup.assoc
d_assoc_222 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_222 = erased
-- Data.Nat.Properties._.IsAbelianGroup.comm
d_comm_224 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_224 = erased
-- Data.Nat.Properties._.IsAbelianGroup.identity
d_identity_226 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_226 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0)))
-- Data.Nat.Properties._.IsAbelianGroup.inverse
d_inverse_232 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_232 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_1052
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0))
-- Data.Nat.Properties._.IsAbelianGroup.isEquivalence
d_isEquivalence_244 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_244 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
               (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0)))))
-- Data.Nat.Properties._.IsAbelianGroup.isGroup
d_isGroup_246 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036
d_isGroup_246 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0)
-- Data.Nat.Properties._.IsAbelianGroup.isMagma
d_isMagma_252 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_252 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
            (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0))))
-- Data.Nat.Properties._.IsAbelianGroup.isMonoid
d_isMonoid_254 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_254 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
      (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0))
-- Data.Nat.Properties._.IsAbelianGroup.isSemigroup
d_isSemigroup_258 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_258 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
         (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v0)))
-- Data.Nat.Properties._.IsAbelianGroup.⁻¹-cong
d_'8315''185''45'cong_276 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_276 = erased
-- Data.Nat.Properties._.IsAbelianGroup.∙-cong
d_'8729''45'cong_278 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_278 = erased
-- Data.Nat.Properties._.IsAlternativeMagma.alter
d_alter_286 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_284 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alter_286 v0
  = coe MAlonzo.Code.Algebra.Structures.d_alter_294 (coe v0)
-- Data.Nat.Properties._.IsAlternativeMagma.isEquivalence
d_isEquivalence_292 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_284 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_292 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_292 (coe v0))
-- Data.Nat.Properties._.IsAlternativeMagma.isMagma
d_isMagma_294 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_284 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_294 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_292 (coe v0)
-- Data.Nat.Properties._.IsAlternativeMagma.∙-cong
d_'8729''45'cong_308 ::
  MAlonzo.Code.Algebra.Structures.T_IsAlternativeMagma_284 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_308 = erased
-- Data.Nat.Properties._.IsBand.assoc
d_assoc_316 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_508 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_316 = erased
-- Data.Nat.Properties._.IsBand.idem
d_idem_318 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_508 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_318 = erased
-- Data.Nat.Properties._.IsBand.isEquivalence
d_isEquivalence_320 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_508 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_320 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v0)))
-- Data.Nat.Properties._.IsBand.isMagma
d_isMagma_322 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_508 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_322 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v0))
-- Data.Nat.Properties._.IsBand.isSemigroup
d_isSemigroup_326 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_508 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_326 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v0)
-- Data.Nat.Properties._.IsBand.∙-cong
d_'8729''45'cong_338 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_508 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_338 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.*-assoc
d_'42''45'assoc_346 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_346 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.*-cancelˡ-nonZero
d_'42''45'cancel'737''45'nonZero_350 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  Integer ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cancel'737''45'nonZero_350 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.*-comm
d_'42''45'comm_352 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_352 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.*-cong
d_'42''45'cong_354 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_354 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.*-identity
d_'42''45'identity_360 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_360 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1494
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1692
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1812
               (coe v0))))
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.assoc
d_assoc_378 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_378 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.comm
d_comm_380 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_380 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.∙-cong
d_'8729''45'cong_382 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_382 = erased
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.identity
d_identity_388 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_388 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1692
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1812
                     (coe v0))))))
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_396 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_396 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1692
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1812
               (coe v0))))
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.isMagma
d_isMagma_400 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_400 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_746
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1692
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1812
                        (coe v0)))))))
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.isMonoid
d_isMonoid_402 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_402 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiring_1692
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1812
                  (coe v0)))))
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.isSemigroup
d_isSemigroup_404 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_404 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1692
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1812
                     (coe v0))))))
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.distrib
d_distrib_408 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_408 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1692
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1812
               (coe v0))))
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.isCommutativeSemiring
d_isCommutativeSemiring_414 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678
d_isCommutativeSemiring_414 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1812
      (coe v0)
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.isEquivalence
d_isEquivalence_418 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_418 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_746
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1692
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1812
                           (coe v0))))))))
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.isSemiring
d_isSemiring_424 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570
d_isSemiring_424 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiring_1692
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1812
         (coe v0))
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_426 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468
d_isSemiringWithoutAnnihilatingZero_426 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1692
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1812
            (coe v0)))
-- Data.Nat.Properties._.IsCancellativeCommutativeSemiring.zero
d_zero_440 ::
  MAlonzo.Code.Algebra.Structures.T_IsCancellativeCommutativeSemiring_1798 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_440 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1586
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1692
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeSemiring_1812
            (coe v0)))
-- Data.Nat.Properties._.IsCommutativeBand.assoc
d_assoc_448 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_448 = erased
-- Data.Nat.Properties._.IsCommutativeBand.comm
d_comm_450 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_450 = erased
-- Data.Nat.Properties._.IsCommutativeBand.idem
d_idem_452 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_452 = erased
-- Data.Nat.Properties._.IsCommutativeBand.isBand
d_isBand_454 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_isBand_454 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v0)
-- Data.Nat.Properties._.IsCommutativeBand.isEquivalence
d_isEquivalence_460 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_460 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v0))))
-- Data.Nat.Properties._.IsCommutativeBand.isMagma
d_isMagma_462 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_462 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v0)))
-- Data.Nat.Properties._.IsCommutativeBand.isSemigroup
d_isSemigroup_466 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_466 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
      (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v0))
-- Data.Nat.Properties._.IsCommutativeBand.∙-cong
d_'8729''45'cong_478 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_478 = erased
-- Data.Nat.Properties._.IsCommutativeMagma.comm
d_comm_486 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_212 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_486 = erased
-- Data.Nat.Properties._.IsCommutativeMagma.isEquivalence
d_isEquivalence_488 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_212 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_488 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_220 (coe v0))
-- Data.Nat.Properties._.IsCommutativeMagma.isMagma
d_isMagma_490 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_212 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_490 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_220 (coe v0)
-- Data.Nat.Properties._.IsCommutativeMagma.∙-cong
d_'8729''45'cong_504 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_212 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_504 = erased
-- Data.Nat.Properties._.IsCommutativeMonoid.assoc
d_assoc_512 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_512 = erased
-- Data.Nat.Properties._.IsCommutativeMonoid.comm
d_comm_514 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_514 = erased
-- Data.Nat.Properties._.IsCommutativeMonoid.identity
d_identity_516 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_516 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v0))
-- Data.Nat.Properties._.IsCommutativeMonoid.isEquivalence
d_isEquivalence_526 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_526 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v0))))
-- Data.Nat.Properties._.IsCommutativeMonoid.isMagma
d_isMagma_528 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_528 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v0)))
-- Data.Nat.Properties._.IsCommutativeMonoid.isMonoid
d_isMonoid_530 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_530 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v0)
-- Data.Nat.Properties._.IsCommutativeMonoid.isSemigroup
d_isSemigroup_534 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_534 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v0))
-- Data.Nat.Properties._.IsCommutativeMonoid.∙-cong
d_'8729''45'cong_548 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_548 = erased
-- Data.Nat.Properties._.IsCommutativeRing.*-assoc
d_'42''45'assoc_558 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_558 = erased
-- Data.Nat.Properties._.IsCommutativeRing.*-comm
d_'42''45'comm_560 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_560 = erased
-- Data.Nat.Properties._.IsCommutativeRing.*-cong
d_'42''45'cong_562 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_562 = erased
-- Data.Nat.Properties._.IsCommutativeRing.*-identity
d_'42''45'identity_568 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_568 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2678
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0))
-- Data.Nat.Properties._.IsCommutativeRing.assoc
d_assoc_586 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_586 = erased
-- Data.Nat.Properties._.IsCommutativeRing.comm
d_comm_588 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_588 = erased
-- Data.Nat.Properties._.IsCommutativeRing.∙-cong
d_'8729''45'cong_590 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_590 = erased
-- Data.Nat.Properties._.IsCommutativeRing.identity
d_identity_596 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_596 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_identity_596 v5
du_identity_596 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_596 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_identity_698
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1144
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
                  (coe v1)))))
-- Data.Nat.Properties._.IsCommutativeRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_602 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132
d_'43''45'isAbelianGroup_602 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0))
-- Data.Nat.Properties._.IsCommutativeRing.isGroup
d_isGroup_610 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036
d_isGroup_610 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isGroup_610 v5
du_isGroup_610 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036
du_isGroup_610 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1144
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
            (coe v1)))
-- Data.Nat.Properties._.IsCommutativeRing.isMagma
d_isMagma_616 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_616 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMagma_616 v5
du_isMagma_616 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_616 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1144
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
                     (coe v1))))))
-- Data.Nat.Properties._.IsCommutativeRing.isMonoid
d_isMonoid_618 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_618 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMonoid_618 v5
du_isMonoid_618 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
du_isMonoid_618 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1144
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
               (coe v1))))
-- Data.Nat.Properties._.IsCommutativeRing.isSemigroup
d_isSemigroup_620 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_620 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isSemigroup_620 v5
du_isSemigroup_620 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_isSemigroup_620 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1144
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
                  (coe v1)))))
-- Data.Nat.Properties._.IsCommutativeRing.⁻¹-cong
d_'8315''185''45'cong_624 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_624 = erased
-- Data.Nat.Properties._.IsCommutativeRing.inverse
d_inverse_626 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_626 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_inverse_626 v5
du_inverse_626 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse_626 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_inverse_1052
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1144
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
               (coe v1))))
-- Data.Nat.Properties._.IsCommutativeRing.distrib
d_distrib_632 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_632 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_2680
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0))
-- Data.Nat.Properties._.IsCommutativeRing.isEquivalence
d_isEquivalence_642 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_642 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isEquivalence_642 v5
du_isEquivalence_642 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_642 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1144
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
                        (coe v1)))))))
-- Data.Nat.Properties._.IsCommutativeRing.isRing
d_isRing_648 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650
d_isRing_648 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0)
-- Data.Nat.Properties._.IsCommutativeRing.isRingWithoutOne
d_isRingWithoutOne_650 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286
d_isRingWithoutOne_650 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isRingWithoutOne_650 v5
du_isRingWithoutOne_650 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2796 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286
du_isRingWithoutOne_650 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2682
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2812 (coe v0))
-- Data.Nat.Properties._.IsCommutativeSemigroup.assoc
d_assoc_680 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_680 = erased
-- Data.Nat.Properties._.IsCommutativeSemigroup.comm
d_comm_682 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_682 = erased
-- Data.Nat.Properties._.IsCommutativeSemigroup.isEquivalence
d_isEquivalence_686 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_686 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v0)))
-- Data.Nat.Properties._.IsCommutativeSemigroup.isMagma
d_isMagma_688 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_688 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v0))
-- Data.Nat.Properties._.IsCommutativeSemigroup.isSemigroup
d_isSemigroup_692 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_692 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_556 (coe v0)
-- Data.Nat.Properties._.IsCommutativeSemigroup.∙-cong
d_'8729''45'cong_704 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_704 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.*-assoc
d_'42''45'assoc_712 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_712 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.*-comm
d_'42''45'comm_714 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_714 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.*-cong
d_'42''45'cong_716 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_716 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.*-identity
d_'42''45'identity_722 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_722 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1494
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v0)))
-- Data.Nat.Properties._.IsCommutativeSemiring.assoc
d_assoc_740 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_740 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.comm
d_comm_742 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_742 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.∙-cong
d_'8729''45'cong_744 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_744 = erased
-- Data.Nat.Properties._.IsCommutativeSemiring.identity
d_identity_750 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_750 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
               (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v0)))))
-- Data.Nat.Properties._.IsCommutativeSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_758 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_758 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v0)))
-- Data.Nat.Properties._.IsCommutativeSemiring.isMagma
d_isMagma_762 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_762 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_746
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v0))))))
-- Data.Nat.Properties._.IsCommutativeSemiring.isMonoid
d_isMonoid_764 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_764 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
            (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v0))))
-- Data.Nat.Properties._.IsCommutativeSemiring.isSemigroup
d_isSemigroup_766 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_766 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
               (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v0)))))
-- Data.Nat.Properties._.IsCommutativeSemiring.distrib
d_distrib_770 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_770 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v0)))
-- Data.Nat.Properties._.IsCommutativeSemiring.isEquivalence
d_isEquivalence_778 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_778 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_746
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v0)))))))
-- Data.Nat.Properties._.IsCommutativeSemiring.isSemiring
d_isSemiring_784 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570
d_isSemiring_784 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v0)
-- Data.Nat.Properties._.IsCommutativeSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_786 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468
d_isSemiringWithoutAnnihilatingZero_786 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v0))
-- Data.Nat.Properties._.IsCommutativeSemiring.zero
d_zero_800 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_800 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1586
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1692 (coe v0))
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.*-assoc
d_'42''45'assoc_812 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1382 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_812 = erased
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.*-comm
d_'42''45'comm_814 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1382 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_814 = erased
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.*-cong
d_'42''45'cong_816 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1382 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_816 = erased
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.comm
d_comm_830 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1382 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_830 = erased
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_834 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1382 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_834 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1316
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1394
         (coe v0))
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.isMonoid
d_isMonoid_838 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1382 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_838 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1316
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1394
            (coe v0)))
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.distrib
d_distrib_842 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1382 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_842 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1322
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1394
         (coe v0))
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.isSemiringWithoutOne
d_isSemiringWithoutOne_850 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1382 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1298
d_isSemiringWithoutOne_850 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1394
      (coe v0)
-- Data.Nat.Properties._.IsCommutativeSemiringWithoutOne.zero
d_zero_864 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1382 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_864 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1324
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutOne_1394
         (coe v0))
-- Data.Nat.Properties._.IsFlexibleMagma.flex
d_flex_872 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_324 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_flex_872 = erased
-- Data.Nat.Properties._.IsFlexibleMagma.isEquivalence
d_isEquivalence_874 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_324 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_874 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_332 (coe v0))
-- Data.Nat.Properties._.IsFlexibleMagma.isMagma
d_isMagma_876 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_324 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_876 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_332 (coe v0)
-- Data.Nat.Properties._.IsFlexibleMagma.∙-cong
d_'8729''45'cong_890 ::
  MAlonzo.Code.Algebra.Structures.T_IsFlexibleMagma_324 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_890 = erased
-- Data.Nat.Properties._.IsGroup.assoc
d_assoc_904 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_904 = erased
-- Data.Nat.Properties._.IsGroup.identity
d_identity_906 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_906 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v0))
-- Data.Nat.Properties._.IsGroup.inverse
d_inverse_912 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_912 v0
  = coe MAlonzo.Code.Algebra.Structures.d_inverse_1052 (coe v0)
-- Data.Nat.Properties._.IsGroup.isEquivalence
d_isEquivalence_918 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_918 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v0))))
-- Data.Nat.Properties._.IsGroup.isMagma
d_isMagma_924 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_924 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v0)))
-- Data.Nat.Properties._.IsGroup.isMonoid
d_isMonoid_926 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_926 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v0)
-- Data.Nat.Properties._.IsGroup.isSemigroup
d_isSemigroup_930 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_930 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v0))
-- Data.Nat.Properties._.IsGroup.⁻¹-cong
d_'8315''185''45'cong_948 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_948 = erased
-- Data.Nat.Properties._.IsGroup.∙-cong
d_'8729''45'cong_950 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_950 = erased
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.assoc
d_assoc_958 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_958 = erased
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.comm
d_comm_960 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_960 = erased
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.idem
d_idem_962 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_962 = erased
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.identity
d_identity_964 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_964 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
            (coe v0)))
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.isCommutativeMonoid
d_isCommutativeMonoid_976 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_isCommutativeMonoid_976 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862 (coe v0)
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.isEquivalence
d_isEquivalence_980 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_980 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_746
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
                  (coe v0)))))
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.isMagma
d_isMagma_984 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_984 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_746
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
               (coe v0))))
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.isMonoid
d_isMonoid_986 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_986 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862 (coe v0))
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.isSemigroup
d_isSemigroup_990 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_990 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
            (coe v0)))
-- Data.Nat.Properties._.IsIdempotentCommutativeMonoid.∙-cong
d_'8729''45'cong_1004 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1004 = erased
-- Data.Nat.Properties._.IsIdempotentMagma.idem
d_idem_1012 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_248 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_1012 = erased
-- Data.Nat.Properties._.IsIdempotentMagma.isEquivalence
d_isEquivalence_1014 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_248 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1014 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_256 (coe v0))
-- Data.Nat.Properties._.IsIdempotentMagma.isMagma
d_isMagma_1016 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_248 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1016 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_256 (coe v0)
-- Data.Nat.Properties._.IsIdempotentMagma.∙-cong
d_'8729''45'cong_1030 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMagma_248 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1030 = erased
-- Data.Nat.Properties._.IsIdempotentMonoid.assoc
d_assoc_1038 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_796 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1038 = erased
-- Data.Nat.Properties._.IsIdempotentMonoid.idem
d_idem_1040 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_796 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_idem_1040 = erased
-- Data.Nat.Properties._.IsIdempotentMonoid.identity
d_identity_1042 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_796 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1042 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_806 (coe v0))
-- Data.Nat.Properties._.IsIdempotentMonoid.isEquivalence
d_isEquivalence_1050 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_796 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1050 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_806 (coe v0))))
-- Data.Nat.Properties._.IsIdempotentMonoid.isMagma
d_isMagma_1052 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_796 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1052 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_806 (coe v0)))
-- Data.Nat.Properties._.IsIdempotentMonoid.isMonoid
d_isMonoid_1054 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_796 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_1054 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMonoid_806 (coe v0)
-- Data.Nat.Properties._.IsIdempotentMonoid.isSemigroup
d_isSemigroup_1058 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_796 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_1058 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_806 (coe v0))
-- Data.Nat.Properties._.IsIdempotentMonoid.∙-cong
d_'8729''45'cong_1072 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_796 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1072 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.*-assoc
d_'42''45'assoc_1080 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1080 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.*-cong
d_'42''45'cong_1082 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1082 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.*-identity
d_'42''45'identity_1088 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1088 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1494
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1936 (coe v0)))
-- Data.Nat.Properties._.IsIdempotentSemiring.assoc
d_assoc_1100 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1100 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.comm
d_comm_1102 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_1102 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.∙-cong
d_'8729''45'cong_1104 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1104 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.+-idem
d_'43''45'idem_1110 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'idem_1110 = erased
-- Data.Nat.Properties._.IsIdempotentSemiring.identity
d_identity_1112 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1112 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
               (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1936 (coe v0)))))
-- Data.Nat.Properties._.IsIdempotentSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1124 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_1124 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1936 (coe v0)))
-- Data.Nat.Properties._.IsIdempotentSemiring.isMagma
d_isMagma_1132 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1132 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_746
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1936 (coe v0))))))
-- Data.Nat.Properties._.IsIdempotentSemiring.isMonoid
d_isMonoid_1134 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_1134 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
            (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1936 (coe v0))))
-- Data.Nat.Properties._.IsIdempotentSemiring.isSemigroup
d_isSemigroup_1136 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_1136 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
               (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1936 (coe v0)))))
-- Data.Nat.Properties._.IsIdempotentSemiring.distrib
d_distrib_1140 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1140 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1936 (coe v0)))
-- Data.Nat.Properties._.IsIdempotentSemiring.isEquivalence
d_isEquivalence_1146 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1146 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_746
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1936 (coe v0)))))))
-- Data.Nat.Properties._.IsIdempotentSemiring.isSemiring
d_isSemiring_1152 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570
d_isSemiring_1152 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1936 (coe v0)
-- Data.Nat.Properties._.IsIdempotentSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_1154 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468
d_isSemiringWithoutAnnihilatingZero_1154 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1936 (coe v0))
-- Data.Nat.Properties._.IsIdempotentSemiring.zero
d_zero_1168 ::
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1168 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1586
      (coe MAlonzo.Code.Algebra.Structures.d_isSemiring_1936 (coe v0))
-- Data.Nat.Properties._.IsInvertibleMagma.inverse
d_inverse_1176 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_924 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1176 v0
  = coe MAlonzo.Code.Algebra.Structures.d_inverse_940 (coe v0)
-- Data.Nat.Properties._.IsInvertibleMagma.isEquivalence
d_isEquivalence_1182 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_924 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1182 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_938 (coe v0))
-- Data.Nat.Properties._.IsInvertibleMagma.isMagma
d_isMagma_1184 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_924 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1184 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_938 (coe v0)
-- Data.Nat.Properties._.IsInvertibleMagma.⁻¹-cong
d_'8315''185''45'cong_1198 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_924 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1198 = erased
-- Data.Nat.Properties._.IsInvertibleMagma.∙-cong
d_'8729''45'cong_1200 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_924 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1200 = erased
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.identity
d_identity_1208 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_976 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1208 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_990 (coe v0)
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.inverse
d_inverse_1214 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_976 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1214 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_940
      (coe
         MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_988 (coe v0))
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.isEquivalence
d_isEquivalence_1220 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_976 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1220 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_938
         (coe
            MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_988 (coe v0)))
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.isInvertibleMagma
d_isInvertibleMagma_1222 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_976 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_924
d_isInvertibleMagma_1222 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_988 (coe v0)
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.isMagma
d_isMagma_1224 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_976 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1224 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_938
      (coe
         MAlonzo.Code.Algebra.Structures.d_isInvertibleMagma_988 (coe v0))
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.⁻¹-cong
d_'8315''185''45'cong_1240 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_976 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1240 = erased
-- Data.Nat.Properties._.IsInvertibleUnitalMagma.∙-cong
d_'8729''45'cong_1242 ::
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_976 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1242 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.*-assoc
d_'42''45'assoc_1250 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1250 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.*-cong
d_'42''45'cong_1252 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1252 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.*-identity
d_'42''45'identity_1258 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1258 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1494
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1936
            (coe
               MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2062
               (coe v0))))
-- Data.Nat.Properties._.IsKleeneAlgebra.assoc
d_assoc_1270 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1270 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.comm
d_comm_1272 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_1272 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.∙-cong
d_'8729''45'cong_1274 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1274 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.+-idem
d_'43''45'idem_1280 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'idem_1280 = erased
-- Data.Nat.Properties._.IsKleeneAlgebra.identity
d_identity_1282 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1282 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1936
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2062
                     (coe v0))))))
-- Data.Nat.Properties._.IsKleeneAlgebra.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_1294 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_1294 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1936
            (coe
               MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2062
               (coe v0))))
-- Data.Nat.Properties._.IsKleeneAlgebra.isMagma
d_isMagma_1302 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1302 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_746
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiring_1936
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2062
                        (coe v0)))))))
-- Data.Nat.Properties._.IsKleeneAlgebra.isMonoid
d_isMonoid_1304 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_1304 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiring_1936
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2062
                  (coe v0)))))
-- Data.Nat.Properties._.IsKleeneAlgebra.isSemigroup
d_isSemigroup_1306 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_1306 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiring_1936
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2062
                     (coe v0))))))
-- Data.Nat.Properties._.IsKleeneAlgebra.distrib
d_distrib_1310 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1310 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiring_1936
            (coe
               MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2062
               (coe v0))))
-- Data.Nat.Properties._.IsKleeneAlgebra.isEquivalence
d_isEquivalence_1316 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1316 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_746
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemiring_1936
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2062
                           (coe v0))))))))
-- Data.Nat.Properties._.IsKleeneAlgebra.isIdempotentSemiring
d_isIdempotentSemiring_1318 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentSemiring_1922
d_isIdempotentSemiring_1318 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2062
      (coe v0)
-- Data.Nat.Properties._.IsKleeneAlgebra.isSemiring
d_isSemiring_1324 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570
d_isSemiring_1324 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiring_1936
      (coe
         MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2062
         (coe v0))
-- Data.Nat.Properties._.IsKleeneAlgebra.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_1326 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468
d_isSemiringWithoutAnnihilatingZero_1326 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1936
         (coe
            MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2062
            (coe v0)))
-- Data.Nat.Properties._.IsKleeneAlgebra.starDestructive
d_starDestructive_1336 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_starDestructive_1336 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_starDestructive_2066 (coe v0)
-- Data.Nat.Properties._.IsKleeneAlgebra.starExpansive
d_starExpansive_1342 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_starExpansive_1342 v0
  = coe MAlonzo.Code.Algebra.Structures.d_starExpansive_2064 (coe v0)
-- Data.Nat.Properties._.IsKleeneAlgebra.zero
d_zero_1352 ::
  MAlonzo.Code.Algebra.Structures.T_IsKleeneAlgebra_2044 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1352 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_1586
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiring_1936
         (coe
            MAlonzo.Code.Algebra.Structures.d_isIdempotentSemiring_2062
            (coe v0)))
-- Data.Nat.Properties._.IsLeftBolLoop.//-cong
d_'47''47''45'cong_1360 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3104 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1360 = erased
-- Data.Nat.Properties._.IsLeftBolLoop.\\-cong
d_'92''92''45'cong_1366 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3104 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1366 = erased
-- Data.Nat.Properties._.IsLeftBolLoop.identity
d_identity_1372 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3104 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1372 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_3042
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3118 (coe v0))
-- Data.Nat.Properties._.IsLeftBolLoop.isEquivalence
d_isEquivalence_1378 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3104 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1378 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_2962
         (coe
            MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
            (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3118 (coe v0))))
-- Data.Nat.Properties._.IsLeftBolLoop.isLoop
d_isLoop_1380 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3104 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026
d_isLoop_1380 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLoop_3118 (coe v0)
-- Data.Nat.Properties._.IsLeftBolLoop.isMagma
d_isMagma_1382 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3104 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1382 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_2962
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3118 (coe v0)))
-- Data.Nat.Properties._.IsLeftBolLoop.isQuasigroup
d_isQuasigroup_1386 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3104 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944
d_isQuasigroup_1386 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3118 (coe v0))
-- Data.Nat.Properties._.IsLeftBolLoop.leftBol
d_leftBol_1388 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3104 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftBol_1388 = erased
-- Data.Nat.Properties._.IsLeftBolLoop.leftDivides
d_leftDivides_1390 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3104 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1390 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_2968
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3118 (coe v0)))
-- Data.Nat.Properties._.IsLeftBolLoop.rightDivides
d_rightDivides_1400 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3104 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1400 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_2970
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3118 (coe v0)))
-- Data.Nat.Properties._.IsLeftBolLoop.∙-cong
d_'8729''45'cong_1412 ::
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3104 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1412 = erased
-- Data.Nat.Properties._.IsLoop.//-cong
d_'47''47''45'cong_1420 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1420 = erased
-- Data.Nat.Properties._.IsLoop.\\-cong
d_'92''92''45'cong_1426 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1426 = erased
-- Data.Nat.Properties._.IsLoop.identity
d_identity_1432 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1432 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_3042 (coe v0)
-- Data.Nat.Properties._.IsLoop.isEquivalence
d_isEquivalence_1438 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1438 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_2962
         (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040 (coe v0)))
-- Data.Nat.Properties._.IsLoop.isMagma
d_isMagma_1440 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1440 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_2962
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040 (coe v0))
-- Data.Nat.Properties._.IsLoop.isQuasigroup
d_isQuasigroup_1444 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944
d_isQuasigroup_1444 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040 (coe v0)
-- Data.Nat.Properties._.IsLoop.leftDivides
d_leftDivides_1446 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1446 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_2968
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040 (coe v0))
-- Data.Nat.Properties._.IsLoop.rightDivides
d_rightDivides_1456 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1456 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_2970
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040 (coe v0))
-- Data.Nat.Properties._.IsLoop.∙-cong
d_'8729''45'cong_1468 ::
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1468 = erased
-- Data.Nat.Properties._.IsMagma.isEquivalence
d_isEquivalence_1476 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1476 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v0)
-- Data.Nat.Properties._.IsMagma.∙-cong
d_'8729''45'cong_1490 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1490 = erased
-- Data.Nat.Properties._.IsMedialMagma.isEquivalence
d_isEquivalence_1498 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_360 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1498 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_368 (coe v0))
-- Data.Nat.Properties._.IsMedialMagma.isMagma
d_isMagma_1500 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_360 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1500 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_368 (coe v0)
-- Data.Nat.Properties._.IsMedialMagma.medial
d_medial_1504 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_360 ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_medial_1504 = erased
-- Data.Nat.Properties._.IsMedialMagma.∙-cong
d_'8729''45'cong_1516 ::
  MAlonzo.Code.Algebra.Structures.T_IsMedialMagma_360 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1516 = erased
-- Data.Nat.Properties._.IsMiddleBolLoop.//-cong
d_'47''47''45'cong_1524 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3358 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1524 = erased
-- Data.Nat.Properties._.IsMiddleBolLoop.\\-cong
d_'92''92''45'cong_1530 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3358 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1530 = erased
-- Data.Nat.Properties._.IsMiddleBolLoop.identity
d_identity_1536 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3358 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1536 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_3042
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3372 (coe v0))
-- Data.Nat.Properties._.IsMiddleBolLoop.isEquivalence
d_isEquivalence_1542 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3358 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1542 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_2962
         (coe
            MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
            (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3372 (coe v0))))
-- Data.Nat.Properties._.IsMiddleBolLoop.isLoop
d_isLoop_1544 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3358 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026
d_isLoop_1544 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLoop_3372 (coe v0)
-- Data.Nat.Properties._.IsMiddleBolLoop.isMagma
d_isMagma_1546 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3358 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1546 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_2962
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3372 (coe v0)))
-- Data.Nat.Properties._.IsMiddleBolLoop.isQuasigroup
d_isQuasigroup_1550 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3358 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944
d_isQuasigroup_1550 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3372 (coe v0))
-- Data.Nat.Properties._.IsMiddleBolLoop.leftDivides
d_leftDivides_1552 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3358 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1552 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_2968
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3372 (coe v0)))
-- Data.Nat.Properties._.IsMiddleBolLoop.middleBol
d_middleBol_1558 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3358 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_middleBol_1558 = erased
-- Data.Nat.Properties._.IsMiddleBolLoop.rightDivides
d_rightDivides_1564 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3358 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1564 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_2970
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3372 (coe v0)))
-- Data.Nat.Properties._.IsMiddleBolLoop.∙-cong
d_'8729''45'cong_1576 ::
  MAlonzo.Code.Algebra.Structures.T_IsMiddleBolLoop_3358 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1576 = erased
-- Data.Nat.Properties._.IsMonoid.assoc
d_assoc_1584 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1584 = erased
-- Data.Nat.Properties._.IsMonoid.identity
d_identity_1586 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1586 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_698 (coe v0)
-- Data.Nat.Properties._.IsMonoid.isEquivalence
d_isEquivalence_1592 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1592 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v0)))
-- Data.Nat.Properties._.IsMonoid.isMagma
d_isMagma_1594 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1594 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v0))
-- Data.Nat.Properties._.IsMonoid.isSemigroup
d_isSemigroup_1598 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_1598 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v0)
-- Data.Nat.Properties._.IsMonoid.∙-cong
d_'8729''45'cong_1612 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1612 = erased
-- Data.Nat.Properties._.IsMoufangLoop.//-cong
d_'47''47''45'cong_1620 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1620 = erased
-- Data.Nat.Properties._.IsMoufangLoop.\\-cong
d_'92''92''45'cong_1626 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1626 = erased
-- Data.Nat.Properties._.IsMoufangLoop.identical
d_identical_1632 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identical_1632 = erased
-- Data.Nat.Properties._.IsMoufangLoop.identity
d_identity_1634 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1634 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_3042
      (coe
         MAlonzo.Code.Algebra.Structures.d_isLoop_3118
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3284 (coe v0)))
-- Data.Nat.Properties._.IsMoufangLoop.isEquivalence
d_isEquivalence_1640 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1640 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_2962
         (coe
            MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
            (coe
               MAlonzo.Code.Algebra.Structures.d_isLoop_3118
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3284 (coe v0)))))
-- Data.Nat.Properties._.IsMoufangLoop.isLeftBolLoop
d_isLeftBolLoop_1642 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  MAlonzo.Code.Algebra.Structures.T_IsLeftBolLoop_3104
d_isLeftBolLoop_1642 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3284 (coe v0)
-- Data.Nat.Properties._.IsMoufangLoop.isLoop
d_isLoop_1644 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026
d_isLoop_1644 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isLoop_3118
      (coe MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3284 (coe v0))
-- Data.Nat.Properties._.IsMoufangLoop.isMagma
d_isMagma_1646 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1646 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_2962
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLoop_3118
            (coe
               MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3284 (coe v0))))
-- Data.Nat.Properties._.IsMoufangLoop.isQuasigroup
d_isQuasigroup_1650 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944
d_isQuasigroup_1650 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
      (coe
         MAlonzo.Code.Algebra.Structures.d_isLoop_3118
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3284 (coe v0)))
-- Data.Nat.Properties._.IsMoufangLoop.leftBol
d_leftBol_1652 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_leftBol_1652 = erased
-- Data.Nat.Properties._.IsMoufangLoop.leftDivides
d_leftDivides_1654 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1654 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_2968
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLoop_3118
            (coe
               MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3284 (coe v0))))
-- Data.Nat.Properties._.IsMoufangLoop.rightBol
d_rightBol_1664 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightBol_1664 = erased
-- Data.Nat.Properties._.IsMoufangLoop.rightDivides
d_rightDivides_1666 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1666 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_2970
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
         (coe
            MAlonzo.Code.Algebra.Structures.d_isLoop_3118
            (coe
               MAlonzo.Code.Algebra.Structures.d_isLeftBolLoop_3284 (coe v0))))
-- Data.Nat.Properties._.IsMoufangLoop.∙-cong
d_'8729''45'cong_1678 ::
  MAlonzo.Code.Algebra.Structures.T_IsMoufangLoop_3268 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1678 = erased
-- Data.Nat.Properties._.IsNearSemiring.*-assoc
d_'42''45'assoc_1686 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1686 = erased
-- Data.Nat.Properties._.IsNearSemiring.*-cong
d_'42''45'cong_1688 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1688 = erased
-- Data.Nat.Properties._.IsNearSemiring.assoc
d_assoc_1698 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1698 = erased
-- Data.Nat.Properties._.IsNearSemiring.∙-cong
d_'8729''45'cong_1700 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1700 = erased
-- Data.Nat.Properties._.IsNearSemiring.identity
d_identity_1706 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1706 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1236 (coe v0))
-- Data.Nat.Properties._.IsNearSemiring.isMagma
d_isMagma_1712 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1712 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1236 (coe v0)))
-- Data.Nat.Properties._.IsNearSemiring.+-isMonoid
d_'43''45'isMonoid_1714 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'43''45'isMonoid_1714 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1236 (coe v0)
-- Data.Nat.Properties._.IsNearSemiring.isSemigroup
d_isSemigroup_1716 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_1716 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1236 (coe v0))
-- Data.Nat.Properties._.IsNearSemiring.distribʳ
d_distrib'691'_1720 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_distrib'691'_1720 = erased
-- Data.Nat.Properties._.IsNearSemiring.isEquivalence
d_isEquivalence_1722 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1722 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_1236 (coe v0))))
-- Data.Nat.Properties._.IsNearSemiring.zeroˡ
d_zero'737'_1736 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1218 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_zero'737'_1736 = erased
-- Data.Nat.Properties._.IsNearring.*-assoc
d_'42''45'assoc_1740 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1740 = erased
-- Data.Nat.Properties._.IsNearring.*-cong
d_'42''45'cong_1742 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1742 = erased
-- Data.Nat.Properties._.IsNearring.*-identity
d_'42''45'identity_1748 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1748 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2208
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2556 (coe v0))
-- Data.Nat.Properties._.IsNearring.assoc
d_assoc_1760 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1760 = erased
-- Data.Nat.Properties._.IsNearring.∙-cong
d_'8729''45'cong_1762 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1762 = erased
-- Data.Nat.Properties._.IsNearring.identity
d_identity_1768 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1768 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2202
         (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2556 (coe v0)))
-- Data.Nat.Properties._.IsNearring.+-inverse
d_'43''45'inverse_1774 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'inverse_1774 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'inverse_2558 (coe v0)
-- Data.Nat.Properties._.IsNearring.isMagma
d_isMagma_1780 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1780 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2202
            (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2556 (coe v0))))
-- Data.Nat.Properties._.IsNearring.+-isMonoid
d_'43''45'isMonoid_1782 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'43''45'isMonoid_1782 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2202
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2556 (coe v0))
-- Data.Nat.Properties._.IsNearring.isSemigroup
d_isSemigroup_1784 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_1784 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2202
         (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2556 (coe v0)))
-- Data.Nat.Properties._.IsNearring.distrib
d_distrib_1788 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1788 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_2210
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2556 (coe v0))
-- Data.Nat.Properties._.IsNearring.isEquivalence
d_isEquivalence_1798 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1798 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2202
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isQuasiring_2556 (coe v0)))))
-- Data.Nat.Properties._.IsNearring.isQuasiring
d_isQuasiring_1802 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180
d_isQuasiring_1802 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2556 (coe v0)
-- Data.Nat.Properties._.IsNearring.zero
d_zero_1814 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1814 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_zero_2212
      (coe MAlonzo.Code.Algebra.Structures.d_isQuasiring_2556 (coe v0))
-- Data.Nat.Properties._.IsNearring.⁻¹-cong
d_'8315''185''45'cong_1820 ::
  MAlonzo.Code.Algebra.Structures.T_IsNearring_2538 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1820 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.*-cong
d_'42''45'cong_1826 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1826 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.*-identity
d_'42''45'identity_1832 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1832 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2434 (coe v0)
-- Data.Nat.Properties._.IsNonAssociativeRing.assoc
d_assoc_1842 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1842 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.comm
d_comm_1844 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_1844 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.∙-cong
d_'8729''45'cong_1846 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1846 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.identity
d_identity_1852 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1852 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1144
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2430
               (coe v0))))
-- Data.Nat.Properties._.IsNonAssociativeRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_1858 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132
d_'43''45'isAbelianGroup_1858 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2430
      (coe v0)
-- Data.Nat.Properties._.IsNonAssociativeRing.isGroup
d_isGroup_1866 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036
d_isGroup_1866 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isGroup_1144
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2430
         (coe v0))
-- Data.Nat.Properties._.IsNonAssociativeRing.isMagma
d_isMagma_1872 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1872 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1144
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2430
                  (coe v0)))))
-- Data.Nat.Properties._.IsNonAssociativeRing.isMonoid
d_isMonoid_1874 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_1874 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1144
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2430
            (coe v0)))
-- Data.Nat.Properties._.IsNonAssociativeRing.isSemigroup
d_isSemigroup_1876 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_1876 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1144
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2430
               (coe v0))))
-- Data.Nat.Properties._.IsNonAssociativeRing.⁻¹-cong
d_'8315''185''45'cong_1880 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_1880 = erased
-- Data.Nat.Properties._.IsNonAssociativeRing.inverse
d_inverse_1882 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_1882 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_1052
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1144
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2430
            (coe v0)))
-- Data.Nat.Properties._.IsNonAssociativeRing.distrib
d_distrib_1888 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_1888 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2436 (coe v0)
-- Data.Nat.Properties._.IsNonAssociativeRing.isEquivalence
d_isEquivalence_1894 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1894 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1144
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2430
                     (coe v0))))))
-- Data.Nat.Properties._.IsNonAssociativeRing.zero
d_zero_1912 ::
  MAlonzo.Code.Algebra.Structures.T_IsNonAssociativeRing_2408 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_1912 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_2438 (coe v0)
-- Data.Nat.Properties._.IsQuasigroup.//-cong
d_'47''47''45'cong_1920 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_1920 = erased
-- Data.Nat.Properties._.IsQuasigroup.\\-cong
d_'92''92''45'cong_1926 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_1926 = erased
-- Data.Nat.Properties._.IsQuasigroup.isEquivalence
d_isEquivalence_1932 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1932 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_2962 (coe v0))
-- Data.Nat.Properties._.IsQuasigroup.isMagma
d_isMagma_1934 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_1934 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_2962 (coe v0)
-- Data.Nat.Properties._.IsQuasigroup.leftDivides
d_leftDivides_1938 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_1938 v0
  = coe MAlonzo.Code.Algebra.Structures.d_leftDivides_2968 (coe v0)
-- Data.Nat.Properties._.IsQuasigroup.rightDivides
d_rightDivides_1948 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_1948 v0
  = coe MAlonzo.Code.Algebra.Structures.d_rightDivides_2970 (coe v0)
-- Data.Nat.Properties._.IsQuasigroup.∙-cong
d_'8729''45'cong_1960 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1960 = erased
-- Data.Nat.Properties._.IsQuasiring.*-assoc
d_'42''45'assoc_1968 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_1968 = erased
-- Data.Nat.Properties._.IsQuasiring.*-cong
d_'42''45'cong_1970 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_1970 = erased
-- Data.Nat.Properties._.IsQuasiring.*-identity
d_'42''45'identity_1976 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1976 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2208 (coe v0)
-- Data.Nat.Properties._.IsQuasiring.assoc
d_assoc_1988 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_1988 = erased
-- Data.Nat.Properties._.IsQuasiring.∙-cong
d_'8729''45'cong_1990 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1990 = erased
-- Data.Nat.Properties._.IsQuasiring.identity
d_identity_1996 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1996 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2202 (coe v0))
-- Data.Nat.Properties._.IsQuasiring.isMagma
d_isMagma_2002 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2002 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2202 (coe v0)))
-- Data.Nat.Properties._.IsQuasiring.+-isMonoid
d_'43''45'isMonoid_2004 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'43''45'isMonoid_2004 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2202 (coe v0)
-- Data.Nat.Properties._.IsQuasiring.isSemigroup
d_isSemigroup_2006 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_2006 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2202 (coe v0))
-- Data.Nat.Properties._.IsQuasiring.distrib
d_distrib_2010 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2010 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2210 (coe v0)
-- Data.Nat.Properties._.IsQuasiring.isEquivalence
d_isEquivalence_2020 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2020 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isMonoid_2202 (coe v0))))
-- Data.Nat.Properties._.IsQuasiring.zero
d_zero_2034 ::
  MAlonzo.Code.Algebra.Structures.T_IsQuasiring_2180 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2034 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_2212 (coe v0)
-- Data.Nat.Properties._.IsRightBolLoop.//-cong
d_'47''47''45'cong_2042 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3186 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''47''45'cong_2042 = erased
-- Data.Nat.Properties._.IsRightBolLoop.\\-cong
d_'92''92''45'cong_2048 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3186 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'92''92''45'cong_2048 = erased
-- Data.Nat.Properties._.IsRightBolLoop.identity
d_identity_2054 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3186 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2054 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_3042
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3200 (coe v0))
-- Data.Nat.Properties._.IsRightBolLoop.isEquivalence
d_isEquivalence_2060 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3186 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2060 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_2962
         (coe
            MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
            (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3200 (coe v0))))
-- Data.Nat.Properties._.IsRightBolLoop.isLoop
d_isLoop_2062 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3186 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026
d_isLoop_2062 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isLoop_3200 (coe v0)
-- Data.Nat.Properties._.IsRightBolLoop.isMagma
d_isMagma_2064 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3186 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2064 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_2962
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3200 (coe v0)))
-- Data.Nat.Properties._.IsRightBolLoop.isQuasigroup
d_isQuasigroup_2068 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3186 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944
d_isQuasigroup_2068 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
      (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3200 (coe v0))
-- Data.Nat.Properties._.IsRightBolLoop.leftDivides
d_leftDivides_2070 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3186 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_leftDivides_2070 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_leftDivides_2968
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3200 (coe v0)))
-- Data.Nat.Properties._.IsRightBolLoop.rightBol
d_rightBol_2080 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3186 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_rightBol_2080 = erased
-- Data.Nat.Properties._.IsRightBolLoop.rightDivides
d_rightDivides_2082 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3186 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_rightDivides_2082 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_rightDivides_2970
      (coe
         MAlonzo.Code.Algebra.Structures.d_isQuasigroup_3040
         (coe MAlonzo.Code.Algebra.Structures.d_isLoop_3200 (coe v0)))
-- Data.Nat.Properties._.IsRightBolLoop.∙-cong
d_'8729''45'cong_2094 ::
  MAlonzo.Code.Algebra.Structures.T_IsRightBolLoop_3186 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2094 = erased
-- Data.Nat.Properties._.IsRing.*-assoc
d_'42''45'assoc_2104 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2104 = erased
-- Data.Nat.Properties._.IsRing.*-cong
d_'42''45'cong_2106 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2106 = erased
-- Data.Nat.Properties._.IsRing.*-identity
d_'42''45'identity_2112 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2112 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2678 (coe v0)
-- Data.Nat.Properties._.IsRing.assoc
d_assoc_2124 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2124 = erased
-- Data.Nat.Properties._.IsRing.comm
d_comm_2126 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2126 = erased
-- Data.Nat.Properties._.IsRing.∙-cong
d_'8729''45'cong_2128 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2128 = erased
-- Data.Nat.Properties._.IsRing.identity
d_identity_2134 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2134 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_identity_2134 v5
du_identity_2134 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_2134 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1144
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
               (coe v0))))
-- Data.Nat.Properties._.IsRing.+-isAbelianGroup
d_'43''45'isAbelianGroup_2140 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132
d_'43''45'isAbelianGroup_2140 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
      (coe v0)
-- Data.Nat.Properties._.IsRing.isGroup
d_isGroup_2148 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036
d_isGroup_2148 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isGroup_2148 v5
du_isGroup_2148 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036
du_isGroup_2148 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isGroup_1144
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
         (coe v0))
-- Data.Nat.Properties._.IsRing.isMagma
d_isMagma_2154 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2154 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMagma_2154 v5
du_isMagma_2154 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_2154 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1144
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
                  (coe v0)))))
-- Data.Nat.Properties._.IsRing.isMonoid
d_isMonoid_2156 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_2156 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMonoid_2156 v5
du_isMonoid_2156 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
du_isMonoid_2156 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1144
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
            (coe v0)))
-- Data.Nat.Properties._.IsRing.isSemigroup
d_isSemigroup_2158 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_2158 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isSemigroup_2158 v5
du_isSemigroup_2158 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_isSemigroup_2158 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1144
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
               (coe v0))))
-- Data.Nat.Properties._.IsRing.⁻¹-cong
d_'8315''185''45'cong_2162 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_2162 = erased
-- Data.Nat.Properties._.IsRing.inverse
d_inverse_2164 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_2164 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_inverse_2164 v5
du_inverse_2164 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse_2164 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_1052
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1144
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
            (coe v0)))
-- Data.Nat.Properties._.IsRing.distrib
d_distrib_2170 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2170 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2680 (coe v0)
-- Data.Nat.Properties._.IsRing.isEquivalence
d_isEquivalence_2176 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2176 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isEquivalence_2176 v5
du_isEquivalence_2176 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_2176 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1144
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2672
                     (coe v0))))))
-- Data.Nat.Properties._.IsRing.isRingWithoutOne
d_isRingWithoutOne_2182 ::
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer -> Integer) ->
  (Integer -> Integer) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2650 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286
d_isRingWithoutOne_2182 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2682 v5
-- Data.Nat.Properties._.IsRingWithoutOne.*-assoc
d_'42''45'assoc_2214 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2214 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.*-cong
d_'42''45'cong_2216 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2216 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.assoc
d_assoc_2226 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2226 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.comm
d_comm_2228 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2228 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.∙-cong
d_'8729''45'cong_2230 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2230 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.identity
d_identity_2236 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2236 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1144
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2304
               (coe v0))))
-- Data.Nat.Properties._.IsRingWithoutOne.+-isAbelianGroup
d_'43''45'isAbelianGroup_2242 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1132
d_'43''45'isAbelianGroup_2242 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2304
      (coe v0)
-- Data.Nat.Properties._.IsRingWithoutOne.isGroup
d_isGroup_2250 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1036
d_isGroup_2250 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isGroup_1144
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2304
         (coe v0))
-- Data.Nat.Properties._.IsRingWithoutOne.isMagma
d_isMagma_2256 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2256 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1144
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2304
                  (coe v0)))))
-- Data.Nat.Properties._.IsRingWithoutOne.isMonoid
d_isMonoid_2258 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_2258 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1144
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2304
            (coe v0)))
-- Data.Nat.Properties._.IsRingWithoutOne.isSemigroup
d_isSemigroup_2260 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_2260 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1144
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2304
               (coe v0))))
-- Data.Nat.Properties._.IsRingWithoutOne.⁻¹-cong
d_'8315''185''45'cong_2264 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8315''185''45'cong_2264 = erased
-- Data.Nat.Properties._.IsRingWithoutOne.inverse
d_inverse_2266 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_2266 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_inverse_1052
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1144
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2304
            (coe v0)))
-- Data.Nat.Properties._.IsRingWithoutOne.distrib
d_distrib_2272 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2272 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_2310 (coe v0)
-- Data.Nat.Properties._.IsRingWithoutOne.isEquivalence
d_isEquivalence_2278 ::
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2286 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2278 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1144
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2304
                     (coe v0))))))
-- Data.Nat.Properties._.IsSelectiveMagma.isEquivalence
d_isEquivalence_2304 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_436 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2304 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_444 (coe v0))
-- Data.Nat.Properties._.IsSelectiveMagma.isMagma
d_isMagma_2306 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_436 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2306 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_444 (coe v0)
-- Data.Nat.Properties._.IsSelectiveMagma.sel
d_sel_2314 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_436 ->
  Integer -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sel_2314 v0
  = coe MAlonzo.Code.Algebra.Structures.d_sel_446 (coe v0)
-- Data.Nat.Properties._.IsSelectiveMagma.∙-cong
d_'8729''45'cong_2322 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_436 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2322 = erased
-- Data.Nat.Properties._.IsSemigroup.assoc
d_assoc_2330 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2330 = erased
-- Data.Nat.Properties._.IsSemigroup.isEquivalence
d_isEquivalence_2332 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2332 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v0))
-- Data.Nat.Properties._.IsSemigroup.isMagma
d_isMagma_2334 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2334 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v0)
-- Data.Nat.Properties._.IsSemigroup.∙-cong
d_'8729''45'cong_2348 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2348 = erased
-- Data.Nat.Properties._.IsSemimedialMagma.isEquivalence
d_isEquivalence_2356 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_396 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2356 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_404 (coe v0))
-- Data.Nat.Properties._.IsSemimedialMagma.isMagma
d_isMagma_2358 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_396 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2358 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_404 (coe v0)
-- Data.Nat.Properties._.IsSemimedialMagma.semiMedial
d_semiMedial_2366 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_396 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_semiMedial_2366 v0
  = coe MAlonzo.Code.Algebra.Structures.d_semiMedial_406 (coe v0)
-- Data.Nat.Properties._.IsSemimedialMagma.∙-cong
d_'8729''45'cong_2378 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemimedialMagma_396 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2378 = erased
-- Data.Nat.Properties._.IsSemiring.*-assoc
d_'42''45'assoc_2386 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2386 = erased
-- Data.Nat.Properties._.IsSemiring.*-cong
d_'42''45'cong_2388 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2388 = erased
-- Data.Nat.Properties._.IsSemiring.*-identity
d_'42''45'identity_2394 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2394 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1494
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe v0))
-- Data.Nat.Properties._.IsSemiring.assoc
d_assoc_2406 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2406 = erased
-- Data.Nat.Properties._.IsSemiring.comm
d_comm_2408 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2408 = erased
-- Data.Nat.Properties._.IsSemiring.∙-cong
d_'8729''45'cong_2410 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2410 = erased
-- Data.Nat.Properties._.IsSemiring.identity
d_identity_2416 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2416 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
               (coe v0))))
-- Data.Nat.Properties._.IsSemiring.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2424 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_2424 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe v0))
-- Data.Nat.Properties._.IsSemiring.isMagma
d_isMagma_2428 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2428 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_746
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
                  (coe v0)))))
-- Data.Nat.Properties._.IsSemiring.isMonoid
d_isMonoid_2430 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_2430 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
            (coe v0)))
-- Data.Nat.Properties._.IsSemiring.isSemigroup
d_isSemigroup_2432 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_2432 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
               (coe v0))))
-- Data.Nat.Properties._.IsSemiring.distrib
d_distrib_2436 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2436 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_1496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
         (coe v0))
-- Data.Nat.Properties._.IsSemiring.isEquivalence
d_isEquivalence_2442 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2442 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_746
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
                     (coe v0))))))
-- Data.Nat.Properties._.IsSemiring.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_2448 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468
d_isSemiringWithoutAnnihilatingZero_2448 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemiringWithoutAnnihilatingZero_1584
      (coe v0)
-- Data.Nat.Properties._.IsSemiring.zero
d_zero_2462 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2462 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_1586 (coe v0)
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.*-assoc
d_'42''45'assoc_2470 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2470 = erased
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.*-cong
d_'42''45'cong_2472 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2472 = erased
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.*-identity
d_'42''45'identity_2478 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_2478 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_1494 (coe v0)
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.assoc
d_assoc_2490 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2490 = erased
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.comm
d_comm_2492 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2492 = erased
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.∙-cong
d_'8729''45'cong_2494 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2494 = erased
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.identity
d_identity_2500 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2500 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
            (coe v0)))
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2508 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_2508 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
      (coe v0)
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.isMagma
d_isMagma_2512 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2512 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_746
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
               (coe v0))))
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.isMonoid
d_isMonoid_2514 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_2514 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
         (coe v0))
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.isSemigroup
d_isSemigroup_2516 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_2516 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
            (coe v0)))
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.distrib
d_distrib_2520 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2520 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_1496 (coe v0)
-- Data.Nat.Properties._.IsSemiringWithoutAnnihilatingZero.isEquivalence
d_isEquivalence_2526 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1468 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2526 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_746
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1488
                  (coe v0)))))
-- Data.Nat.Properties._.IsSemiringWithoutOne.*-assoc
d_'42''45'assoc_2546 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1298 ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_2546 = erased
-- Data.Nat.Properties._.IsSemiringWithoutOne.*-cong
d_'42''45'cong_2548 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1298 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cong_2548 = erased
-- Data.Nat.Properties._.IsSemiringWithoutOne.comm
d_comm_2558 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1298 ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_comm_2558 = erased
-- Data.Nat.Properties._.IsSemiringWithoutOne.+-isCommutativeMonoid
d_'43''45'isCommutativeMonoid_2562 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1298 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'43''45'isCommutativeMonoid_2562 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1316
      (coe v0)
-- Data.Nat.Properties._.IsSemiringWithoutOne.isMonoid
d_isMonoid_2566 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1298 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_2566 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_'43''45'isCommutativeMonoid_1316
         (coe v0))
-- Data.Nat.Properties._.IsSemiringWithoutOne.distrib
d_distrib_2570 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1298 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_2570 v0
  = coe MAlonzo.Code.Algebra.Structures.d_distrib_1322 (coe v0)
-- Data.Nat.Properties._.IsSemiringWithoutOne.zero
d_zero_2590 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1298 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_2590 v0
  = coe MAlonzo.Code.Algebra.Structures.d_zero_1324 (coe v0)
-- Data.Nat.Properties._.IsUnitalMagma.identity
d_identity_2616 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_642 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_2616 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_654 (coe v0)
-- Data.Nat.Properties._.IsUnitalMagma.isEquivalence
d_isEquivalence_2622 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_642 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_2622 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_652 (coe v0))
-- Data.Nat.Properties._.IsUnitalMagma.isMagma
d_isMagma_2624 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_642 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2624 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_652 (coe v0)
-- Data.Nat.Properties._.IsUnitalMagma.∙-cong
d_'8729''45'cong_2638 ::
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_642 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_2638 = erased
-- Data.Nat.Properties.nonZero?
d_nonZero'63'_2652 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_nonZero'63'_2652 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe
                   MAlonzo.Code.Data.Nat.Base.C_NonZero'46'constructor_3581
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
-- Data.Nat.Properties.nonTrivial?
d_nonTrivial'63'_2656 ::
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_nonTrivial'63'_2656 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      1 -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe
                   MAlonzo.Code.Data.Nat.Base.C_NonTrivial'46'constructor_5677
                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
-- Data.Nat.Properties.suc-injective
d_suc'45'injective_2660 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45'injective_2660 = erased
-- Data.Nat.Properties.≡ᵇ⇒≡
d_'8801''7495''8658''8801'_2666 ::
  Integer ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''7495''8658''8801'_2666 = erased
-- Data.Nat.Properties.≡⇒≡ᵇ
d_'8801''8658''8801''7495'_2678 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_'8801''8658''8801''7495'_2678 v0 ~v1 ~v2
  = du_'8801''8658''8801''7495'_2678 v0
du_'8801''8658''8801''7495'_2678 :: Integer -> AgdaAny
du_'8801''8658''8801''7495'_2678 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe du_'8801''8658''8801''7495'_2678 (coe v1))
-- Data.Nat.Properties._≟_
d__'8799'__2688 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__2688 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
      erased (\ v2 -> coe du_'8801''8658''8801''7495'_2678 (coe v0))
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_66
         (coe eqInt (coe v0) (coe v1)))
-- Data.Nat.Properties.≡-irrelevant
d_'8801''45'irrelevant_2694 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''45'irrelevant_2694 = erased
-- Data.Nat.Properties.≟-diag
d_'8799''45'diag_2698 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8799''45'diag_2698 = erased
-- Data.Nat.Properties.≡-isDecEquivalence
d_'8801''45'isDecEquivalence_2700 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
d_'8801''45'isDecEquivalence_2700
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecEquivalence'46'constructor_3075
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (coe d__'8799'__2688)
-- Data.Nat.Properties.≡-decSetoid
d_'8801''45'decSetoid_2702 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84
d_'8801''45'decSetoid_2702
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecSetoid'46'constructor_1377
      d_'8801''45'isDecEquivalence_2700
-- Data.Nat.Properties.0≢1+n
d_0'8802'1'43'n_2704 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_0'8802'1'43'n_2704 = erased
-- Data.Nat.Properties.1+n≢0
d_1'43'n'8802'0_2706 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_1'43'n'8802'0_2706 = erased
-- Data.Nat.Properties.1+n≢n
d_1'43'n'8802'n_2708 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_1'43'n'8802'n_2708 = erased
-- Data.Nat.Properties.<ᵇ⇒<
d_'60''7495''8658''60'_2716 ::
  Integer ->
  Integer -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''7495''8658''60'_2716 v0 ~v1 ~v2
  = du_'60''7495''8658''60'_2716 v0
du_'60''7495''8658''60'_2716 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''7495''8658''60'_2716 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (coe du_'60''7495''8658''60'_2716 (coe v1)))
-- Data.Nat.Properties.<⇒<ᵇ
d_'60''8658''60''7495'_2728 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_'60''8658''60''7495'_2728 ~v0 ~v1 v2
  = du_'60''8658''60''7495'_2728 v2
du_'60''8658''60''7495'_2728 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
du_'60''8658''60''7495'_2728 v0
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v3
        -> case coe v3 of
             MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
               -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
               -> coe
                    du_'60''8658''60''7495'_2728
                    (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.<ᵇ-reflects-<
d_'60''7495''45'reflects'45''60'_2736 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Reflects.T_Reflects_16
d_'60''7495''45'reflects'45''60'_2736 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Reflects.du_fromEquivalence_132
      (coe ltInt (coe v0) (coe v1))
      (\ v2 -> coe du_'60''7495''8658''60'_2716 (coe v0))
      (coe du_'60''8658''60''7495'_2728)
-- Data.Nat.Properties.≤ᵇ⇒≤
d_'8804''7495''8658''8804'_2746 ::
  Integer ->
  Integer -> AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''7495''8658''8804'_2746 v0 ~v1 ~v2
  = du_'8804''7495''8658''8804'_2746 v0
du_'8804''7495''8658''8804'_2746 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''7495''8658''8804'_2746 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe du_'60''7495''8658''60'_2716 (coe v1))
-- Data.Nat.Properties.≤⇒≤ᵇ
d_'8804''8658''8804''7495'_2758 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_'8804''8658''8804''7495'_2758 ~v0 ~v1 v2
  = du_'8804''8658''8804''7495'_2758 v2
du_'8804''8658''8804''7495'_2758 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
du_'8804''8658''8804''7495'_2758 v0
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v3
        -> coe
             du_'60''8658''60''7495'_2728
             (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.≤ᵇ-reflects-≤
d_'8804''7495''45'reflects'45''8804'_2766 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Reflects.T_Reflects_16
d_'8804''7495''45'reflects'45''8804'_2766 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Reflects.du_fromEquivalence_132
      (coe
         MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v0) (coe v1))
      (\ v2 -> coe du_'8804''7495''8658''8804'_2746 (coe v0))
      (coe du_'8804''8658''8804''7495'_2758)
-- Data.Nat.Properties.≤-reflexive
d_'8804''45'reflexive_2772 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'reflexive_2772 v0 ~v1 ~v2
  = du_'8804''45'reflexive_2772 v0
du_'8804''45'reflexive_2772 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'reflexive_2772 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (coe du_'8804''45'reflexive_2772 (coe v1)))
-- Data.Nat.Properties.≤-refl
d_'8804''45'refl_2776 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'refl_2776 v0 = coe du_'8804''45'reflexive_2772 (coe v0)
-- Data.Nat.Properties.≤-antisym
d_'8804''45'antisym_2778 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''45'antisym_2778 = erased
-- Data.Nat.Properties.≤-trans
d_'8804''45'trans_2784 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'trans_2784 ~v0 ~v1 ~v2 v3 v4
  = du_'8804''45'trans_2784 v3 v4
du_'8804''45'trans_2784 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'trans_2784 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
        -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v7
               -> coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (coe du_'8804''45'trans_2784 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.≤-total
d_'8804''45'total_2790 ::
  Integer -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8804''45'total_2790 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                       (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Sum.Base.du_map_84
                          (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34)
                          (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34)
                          (d_'8804''45'total_2790 (coe v2) (coe v3))))
-- Data.Nat.Properties.≤-irrelevant
d_'8804''45'irrelevant_2796 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''45'irrelevant_2796 = erased
-- Data.Nat.Properties._≤?_
d__'8804''63'__2802 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''63'__2802 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
      (\ v2 -> coe du_'8804''7495''8658''8804'_2746 (coe v0))
      (coe du_'8804''8658''8804''7495'_2758)
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_66
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v0) (coe v1)))
-- Data.Nat.Properties._≥?_
d__'8805''63'__2808 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8805''63'__2808 v0 v1
  = coe d__'8804''63'__2802 (coe v1) (coe v0)
-- Data.Nat.Properties.≤-isPreorder
d_'8804''45'isPreorder_2810 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_'8804''45'isPreorder_2810
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPreorder'46'constructor_3993
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (\ v0 v1 v2 -> coe du_'8804''45'reflexive_2772 v0)
      (\ v0 v1 v2 v3 v4 -> coe du_'8804''45'trans_2784 v3 v4)
-- Data.Nat.Properties.≤-isTotalPreorder
d_'8804''45'isTotalPreorder_2812 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_124
d_'8804''45'isTotalPreorder_2812
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsTotalPreorder'46'constructor_8307
      (coe d_'8804''45'isPreorder_2810) (coe d_'8804''45'total_2790)
-- Data.Nat.Properties.≤-isPartialOrder
d_'8804''45'isPartialOrder_2814 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_'8804''45'isPartialOrder_2814
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPartialOrder'46'constructor_9831
      (coe d_'8804''45'isPreorder_2810) erased
-- Data.Nat.Properties.≤-isTotalOrder
d_'8804''45'isTotalOrder_2816 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404
d_'8804''45'isTotalOrder_2816
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsTotalOrder'46'constructor_20499
      (coe d_'8804''45'isPartialOrder_2814) (coe d_'8804''45'total_2790)
-- Data.Nat.Properties.≤-isDecTotalOrder
d_'8804''45'isDecTotalOrder_2818 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460
d_'8804''45'isDecTotalOrder_2818
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecTotalOrder'46'constructor_22635
      (coe d_'8804''45'isTotalOrder_2816) (coe d__'8799'__2688)
      (coe d__'8804''63'__2802)
-- Data.Nat.Properties.≤-preorder
d_'8804''45'preorder_2820 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_'8804''45'preorder_2820
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Preorder'46'constructor_2249
      d_'8804''45'isPreorder_2810
-- Data.Nat.Properties.≤-totalPreorder
d_'8804''45'totalPreorder_2822 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222
d_'8804''45'totalPreorder_2822
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_TotalPreorder'46'constructor_4543
      d_'8804''45'isTotalPreorder_2812
-- Data.Nat.Properties.≤-poset
d_'8804''45'poset_2824 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_'8804''45'poset_2824
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Poset'46'constructor_6347
      d_'8804''45'isPartialOrder_2814
-- Data.Nat.Properties.≤-totalOrder
d_'8804''45'totalOrder_2826 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764
d_'8804''45'totalOrder_2826
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_TotalOrder'46'constructor_15657
      d_'8804''45'isTotalOrder_2816
-- Data.Nat.Properties.≤-decTotalOrder
d_'8804''45'decTotalOrder_2828 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866
d_'8804''45'decTotalOrder_2828
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecTotalOrder'46'constructor_17747
      d_'8804''45'isDecTotalOrder_2818
-- Data.Nat.Properties.s≤s-injective
d_s'8804's'45'injective_2834 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_s'8804's'45'injective_2834 = erased
-- Data.Nat.Properties.≤-pred
d_'8804''45'pred_2836 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'pred_2836 ~v0 ~v1 = du_'8804''45'pred_2836
du_'8804''45'pred_2836 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'pred_2836
  = coe MAlonzo.Code.Data.Nat.Base.du_s'8804's'8315''185'_62
-- Data.Nat.Properties.m≤n⇒m≤1+n
d_m'8804'n'8658'm'8804'1'43'n_2838 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'n'8658'm'8804'1'43'n_2838 ~v0 ~v1 v2
  = du_m'8804'n'8658'm'8804'1'43'n_2838 v2
du_m'8804'n'8658'm'8804'1'43'n_2838 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'n'8658'm'8804'1'43'n_2838 v0 = coe v0
-- Data.Nat.Properties.n≤1+n
d_n'8804'1'43'n_2844 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'8804'1'43'n_2844 v0 = coe d_'8804''45'refl_2776 (coe v0)
-- Data.Nat.Properties.1+n≰n
d_1'43'n'8816'n_2846 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_1'43'n'8816'n_2846 = erased
-- Data.Nat.Properties.n≤0⇒n≡0
d_n'8804'0'8658'n'8801'0_2850 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'8804'0'8658'n'8801'0_2850 = erased
-- Data.Nat.Properties.n≤1⇒n≡0∨n≡1
d_n'8804'1'8658'n'8801'0'8744'n'8801'1_2852 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_n'8804'1'8658'n'8801'0'8744'n'8801'1_2852 ~v0 v1
  = du_n'8804'1'8658'n'8801'0'8744'n'8801'1_2852 v1
du_n'8804'1'8658'n'8801'0'8744'n'8801'1_2852 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_n'8804'1'8658'n'8801'0'8744'n'8801'1_2852 v0
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
        -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v3
        -> coe
             seq (coe v3) (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.<⇒≤
d_'60''8658''8804'_2854 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''8658''8804'_2854 ~v0 ~v1 v2 = du_'60''8658''8804'_2854 v2
du_'60''8658''8804'_2854 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''8658''8804'_2854 v0
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v3
        -> case coe v3 of
             MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
               -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
               -> coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (coe
                       du_'60''8658''8804'_2854
                       (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.<⇒≢
d_'60''8658''8802'_2858 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8802'_2858 = erased
-- Data.Nat.Properties.>⇒≢
d_'62''8658''8802'_2862 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'62''8658''8802'_2862 = erased
-- Data.Nat.Properties.≤⇒≯
d_'8804''8658''8815'_2864 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8804''8658''8815'_2864 = erased
-- Data.Nat.Properties.<⇒≱
d_'60''8658''8817'_2870 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8817'_2870 = erased
-- Data.Nat.Properties.<⇒≯
d_'60''8658''8815'_2876 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8815'_2876 = erased
-- Data.Nat.Properties.≰⇒≮
d_'8816''8658''8814'_2882 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8816''8658''8814'_2882 = erased
-- Data.Nat.Properties.≰⇒>
d_'8816''8658''62'_2888 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8816''8658''62'_2888 v0 v1 ~v2 = du_'8816''8658''62'_2888 v0 v1
du_'8816''8658''62'_2888 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8816''8658''62'_2888 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
             erased
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (coe du_'8816''8658''62'_2888 (coe v2) (coe v3))))
-- Data.Nat.Properties.≰⇒≥
d_'8816''8658''8805'_2900 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8816''8658''8805'_2900 v0 v1 ~v2
  = du_'8816''8658''8805'_2900 v0 v1
du_'8816''8658''8805'_2900 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8816''8658''8805'_2900 v0 v1
  = coe
      du_'60''8658''8804'_2854
      (coe du_'8816''8658''62'_2888 (coe v0) (coe v1))
-- Data.Nat.Properties.≮⇒≥
d_'8814''8658''8805'_2902 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8814''8658''8805'_2902 v0 v1 ~v2
  = du_'8814''8658''8805'_2902 v0 v1
du_'8814''8658''8805'_2902 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8814''8658''8805'_2902 v0 v1
  = case coe v1 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                0 -> coe
                       MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                       erased
                _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (coe du_'8814''8658''8805'_2902 (coe v3) (coe v2))))
-- Data.Nat.Properties.≤∧≢⇒<
d_'8804''8743''8802''8658''60'_2918 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''8743''8802''8658''60'_2918 ~v0 v1 v2 ~v3
  = du_'8804''8743''8802''8658''60'_2918 v1 v2
du_'8804''8743''8802''8658''60'_2918 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''8743''8802''8658''60'_2918 v0 v1
  = case coe v0 of
      0 -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                erased)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                  -> coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5
                  -> coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (coe du_'8804''8743''8802''8658''60'_2918 (coe v2) (coe v5))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.≤∧≮⇒≡
d_'8804''8743''8814''8658''8801'_2936 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  (MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8743''8814''8658''8801'_2936 = erased
-- Data.Nat.Properties.≤-<-connex
d_'8804''45''60''45'connex_2942 ::
  Integer -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8804''45''60''45'connex_2942 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
              (\ v2 -> coe du_'8804''7495''8658''8804'_2746 (coe v0))
              (coe du_'8804''8658''8804''7495'_2758)
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_66
                 (coe
                    MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v0)
                    (coe v1))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v5
                         -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v5)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                          (coe du_'8816''8658''62'_2888 (coe v0) (coe v1)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.≥->-connex
d_'8805''45''62''45'connex_2964 ::
  Integer -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8805''45''62''45'connex_2964 v0 v1
  = coe d_'8804''45''60''45'connex_2942 (coe v1) (coe v0)
-- Data.Nat.Properties.<-≤-connex
d_'60''45''8804''45'connex_2966 ::
  Integer -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'60''45''8804''45'connex_2966
  = coe
      MAlonzo.Code.Relation.Binary.Consequences.du_flip'45'Connex_854
      (coe d_'8804''45''60''45'connex_2942)
-- Data.Nat.Properties.>-≥-connex
d_'62''45''8805''45'connex_2968 ::
  Integer -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'62''45''8805''45'connex_2968
  = coe
      MAlonzo.Code.Relation.Binary.Consequences.du_flip'45'Connex_854
      (coe d_'8805''45''62''45'connex_2964)
-- Data.Nat.Properties.<-irrefl
d_'60''45'irrefl_2970 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'irrefl_2970 = erased
-- Data.Nat.Properties.<-asym
d_'60''45'asym_2974 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'asym_2974 = erased
-- Data.Nat.Properties.<-trans
d_'60''45'trans_2980 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'trans_2980 ~v0 v1 ~v2 v3 v4
  = du_'60''45'trans_2980 v1 v3 v4
du_'60''45'trans_2980 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45'trans_2980 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5
        -> let v6 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9
                  -> coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (coe
                          du_'8804''45'trans_2784 (coe v5)
                          (coe
                             du_'8804''45'trans_2784 (coe d_n'8804'1'43'n_2844 (coe v6))
                             (coe v9)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.≤-<-trans
d_'8804''45''60''45'trans_2986 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45''60''45'trans_2986 ~v0 ~v1 ~v2 v3 v4
  = du_'8804''45''60''45'trans_2986 v3 v4
du_'8804''45''60''45'trans_2986 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45''60''45'trans_2986 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v4
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe du_'8804''45'trans_2784 (coe v0) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.<-≤-trans
d_'60''45''8804''45'trans_2992 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45''8804''45'trans_2992 ~v0 ~v1 ~v2 v3 v4
  = du_'60''45''8804''45'trans_2992 v3 v4
du_'60''45''8804''45'trans_2992 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45''8804''45'trans_2992 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v7
               -> coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (coe du_'8804''45'trans_2784 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.<-cmp
d_'60''45'cmp_2998 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_'60''45'cmp_2998 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
              erased (\ v2 -> coe du_'8801''8658''8801''7495'_2678 (coe v0))
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_66
                 (coe eqInt (coe v0) (coe v1))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v5
                         -> coe MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v5
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v4)
                       (let v5 = ltInt (coe v0) (coe v1) in
                        coe
                          (if coe v5
                             then coe
                                    seq
                                    (coe
                                       MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_66
                                       (coe v5))
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                                       (coe du_'60''7495''8658''60'_2716 (coe v0)))
                             else coe
                                    seq
                                    (coe
                                       MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_66
                                       (coe v5))
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                                       (coe
                                          du_'8804''8743''8802''8658''60'_2918 (coe v0)
                                          (coe du_'8814''8658''8805'_2902 (coe v0) (coe v1))))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties._<?_
d__'60''63'__3030 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__3030 v0 v1
  = coe
      d__'8804''63'__2802 (coe addInt (coe (1 :: Integer)) (coe v0))
      (coe v1)
-- Data.Nat.Properties._>?_
d__'62''63'__3036 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'62''63'__3036 v0 v1 = coe d__'60''63'__3030 (coe v1) (coe v0)
-- Data.Nat.Properties.<-irrelevant
d_'60''45'irrelevant_3038 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''45'irrelevant_3038 = erased
-- Data.Nat.Properties.<-resp₂-≡
d_'60''45'resp'8322''45''8801'_3040 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'8322''45''8801'_3040
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe (\ v0 v1 v2 v3 v4 -> v4)) (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Nat.Properties.<-isStrictPartialOrder
d_'60''45'isStrictPartialOrder_3046 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
d_'60''45'isStrictPartialOrder_3046
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictPartialOrder'46'constructor_14011
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (\ v0 v1 v2 v3 v4 -> coe du_'60''45'trans_2980 v1 v3 v4)
      d_'60''45'resp'8322''45''8801'_3040
-- Data.Nat.Properties.<-isStrictTotalOrder
d_'60''45'isStrictTotalOrder_3048 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
d_'60''45'isStrictTotalOrder_3048
  = coe
      MAlonzo.Code.Relation.Binary.Structures.Biased.du_isStrictTotalOrder'7580'_538
      (coe
         MAlonzo.Code.Relation.Binary.Structures.Biased.C_IsStrictTotalOrder'7580''46'constructor_6029
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
         (\ v0 v1 v2 v3 v4 -> coe du_'60''45'trans_2980 v1 v3 v4)
         (coe d_'60''45'cmp_2998))
-- Data.Nat.Properties.<-strictPartialOrder
d_'60''45'strictPartialOrder_3050 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556
d_'60''45'strictPartialOrder_3050
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictPartialOrder'46'constructor_11031
      d_'60''45'isStrictPartialOrder_3046
-- Data.Nat.Properties.<-strictTotalOrder
d_'60''45'strictTotalOrder_3052 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036
d_'60''45'strictTotalOrder_3052
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictTotalOrder'46'constructor_20945
      d_'60''45'isStrictTotalOrder_3048
-- Data.Nat.Properties.s<s-injective
d_s'60's'45'injective_3058 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_s'60's'45'injective_3058 = erased
-- Data.Nat.Properties.<-pred
d_'60''45'pred_3060 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'pred_3060 ~v0 ~v1 = du_'60''45'pred_3060
du_'60''45'pred_3060 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''45'pred_3060
  = coe MAlonzo.Code.Data.Nat.Base.du_s'60's'8315''185'_70
-- Data.Nat.Properties.m<n⇒m<1+n
d_m'60'n'8658'm'60'1'43'n_3062 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'8658'm'60'1'43'n_3062 ~v0 ~v1 v2
  = du_m'60'n'8658'm'60'1'43'n_3062 v2
du_m'60'n'8658'm'60'1'43'n_3062 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'n'8658'm'60'1'43'n_3062 v0
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v3
        -> case coe v3 of
             MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
               -> coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
               -> coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (coe
                       du_m'60'n'8658'm'60'1'43'n_3062
                       (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.n≮0
d_n'8814'0_3066 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8814'0_3066 = erased
-- Data.Nat.Properties.n≮n
d_n'8814'n_3070 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'8814'n_3070 = erased
-- Data.Nat.Properties.0<1+n
d_0'60'1'43'n_3074 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'1'43'n_3074 ~v0 = du_0'60'1'43'n_3074
du_0'60'1'43'n_3074 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'1'43'n_3074
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
-- Data.Nat.Properties.n<1+n
d_n'60'1'43'n_3078 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'60'1'43'n_3078 v0
  = coe
      d_'8804''45'refl_2776 (coe addInt (coe (1 :: Integer)) (coe v0))
-- Data.Nat.Properties.n<1⇒n≡0
d_n'60'1'8658'n'8801'0_3082 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'60'1'8658'n'8801'0_3082 = erased
-- Data.Nat.Properties.n>0⇒n≢0
d_n'62'0'8658'n'8802'0_3086 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_n'62'0'8658'n'8802'0_3086 = erased
-- Data.Nat.Properties.n≢0⇒n>0
d_n'8802'0'8658'n'62'0_3090 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'8802'0'8658'n'62'0_3090 v0 ~v1
  = du_n'8802'0'8658'n'62'0_3090 v0
du_n'8802'0'8658'n'62'0_3090 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_n'8802'0'8658'n'62'0_3090 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
             erased
      _ -> coe du_0'60'1'43'n_3074
-- Data.Nat.Properties.m<n⇒0<n
d_m'60'n'8658'0'60'n_3096 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'8658'0'60'n_3096 ~v0 ~v1 = du_m'60'n'8658'0'60'n_3096
du_m'60'n'8658'0'60'n_3096 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'n'8658'0'60'n_3096
  = coe du_'8804''45'trans_2784 (coe du_0'60'1'43'n_3074)
-- Data.Nat.Properties.m<n⇒n≢0
d_m'60'n'8658'n'8802'0_3098 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_m'60'n'8658'n'8802'0_3098 = erased
-- Data.Nat.Properties.m<n⇒m≤1+n
d_m'60'n'8658'm'8804'1'43'n_3102 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'8658'm'8804'1'43'n_3102 ~v0 ~v1 v2
  = du_m'60'n'8658'm'8804'1'43'n_3102 v2
du_m'60'n'8658'm'8804'1'43'n_3102 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'n'8658'm'8804'1'43'n_3102 v0
  = coe du_'60''8658''8804'_2854 (coe v0)
-- Data.Nat.Properties.m<1+n⇒m<n∨m≡n
d_m'60'1'43'n'8658'm'60'n'8744'm'8801'n_3108 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_m'60'1'43'n'8658'm'60'n'8744'm'8801'n_3108 v0 v1 v2
  = case coe v0 of
      0 -> case coe v1 of
             0 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
             _ -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe du_0'60'1'43'n_3074)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
                  -> let v7 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Sum.Base.du_map_84
                          (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34) erased
                          (d_m'60'1'43'n'8658'm'60'n'8744'm'8801'n_3108
                             (coe v3) (coe v7) (coe v6)))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.m≤n⇒m<n∨m≡n
d_m'8804'n'8658'm'60'n'8744'm'8801'n_3118 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_m'8804'n'8658'm'60'n'8744'm'8801'n_3118 v0 v1 v2
  = coe
      d_m'60'1'43'n'8658'm'60'n'8744'm'8801'n_3108 (coe v0) (coe v1)
      (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v2)
-- Data.Nat.Properties.m<1+n⇒m≤n
d_m'60'1'43'n'8658'm'8804'n_3122 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'1'43'n'8658'm'8804'n_3122 ~v0 ~v1 v2
  = du_m'60'1'43'n'8658'm'8804'n_3122 v2
du_m'60'1'43'n'8658'm'8804'n_3122 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'1'43'n'8658'm'8804'n_3122 v0
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.∀[m≤n⇒m≢o]⇒n<o
d_'8704''91'm'8804'n'8658'm'8802'o'93''8658'n'60'o_3132 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8704''91'm'8804'n'8658'm'8802'o'93''8658'n'60'o_3132 v0 v1 ~v2
  = du_'8704''91'm'8804'n'8658'm'8802'o'93''8658'n'60'o_3132 v0 v1
du_'8704''91'm'8804'n'8658'm'8802'o'93''8658'n'60'o_3132 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8704''91'm'8804'n'8658'm'8802'o'93''8658'n'60'o_3132 v0 v1
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
             erased
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                0 -> coe du_0'60'1'43'n_3074
                _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (coe
                             du_'8704''91'm'8804'n'8658'm'8802'o'93''8658'n'60'o_3132 (coe v3)
                             (coe v2))))
-- Data.Nat.Properties._.rec
d_rec_3150 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_rec_3150 = erased
-- Data.Nat.Properties.∀[m<n⇒m≢o]⇒n≤o
d_'8704''91'm'60'n'8658'm'8802'o'93''8658'n'8804'o_3160 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8704''91'm'60'n'8658'm'8802'o'93''8658'n'8804'o_3160 v0 v1 ~v2
  = du_'8704''91'm'60'n'8658'm'8802'o'93''8658'n'8804'o_3160 v0 v1
du_'8704''91'm'60'n'8658'm'8802'o'93''8658'n'8804'o_3160 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8704''91'm'60'n'8658'm'8802'o'93''8658'n'8804'o_3160 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe
                       MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                       erased
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (coe
                             du_'8704''91'm'60'n'8658'm'8802'o'93''8658'n'8804'o_3160 (coe v2)
                             (coe v3))))
-- Data.Nat.Properties._.rec
d_rec_3180 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_rec_3180 = erased
-- Data.Nat.Properties.≤-Reasoning._._IsRelatedTo_
d__IsRelatedTo__3188 a0 a1 = ()
-- Data.Nat.Properties.≤-Reasoning._._∎
d__'8718'_3190 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d__'8718'_3190
  = let v0 = d_'8804''45'isPreorder_2810 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
            (coe v0)))
-- Data.Nat.Properties.≤-Reasoning._.<-go
d_'60''45'go_3192 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'60''45'go_3192
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
      (\ v0 v1 v2 v3 v4 -> coe du_'60''45'trans_2980 v1 v3 v4)
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
      (\ v0 v1 v2 v3 v4 -> coe du_'60''45''8804''45'trans_2992 v3 v4)
-- Data.Nat.Properties.≤-Reasoning._.IsEquality
d_IsEquality_3194 a0 a1 a2 = ()
-- Data.Nat.Properties.≤-Reasoning._.IsEquality?
d_IsEquality'63'_3196 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_IsEquality'63'_3196 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_IsEquality'63'_224
      v2
-- Data.Nat.Properties.≤-Reasoning._.IsStrict
d_IsStrict_3198 a0 a1 a2 = ()
-- Data.Nat.Properties.≤-Reasoning._.IsStrict?
d_IsStrict'63'_3200 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_IsStrict'63'_3200 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_IsStrict'63'_188
      v2
-- Data.Nat.Properties.≤-Reasoning._.begin_
d_begin__3202 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_begin__3202
  = let v0 = d_'8804''45'isPreorder_2810 in
    coe
      (let v1 = \ v1 v2 v3 -> coe du_'60''8658''8804'_2854 v3 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
               (coe v0) (coe v1))))
-- Data.Nat.Properties.≤-Reasoning._.begin-contradiction_
d_begin'45'contradiction__3204 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny
d_begin'45'contradiction__3204 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin'45'contradiction__246
-- Data.Nat.Properties.≤-Reasoning._.begin_
d_begin__3206 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_begin__3206 = erased
-- Data.Nat.Properties.≤-Reasoning._.begin_
d_begin__3208 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_begin__3208
  = let v0
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
    coe
      (\ v1 v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
           (coe v0) v1 v2 v3)
-- Data.Nat.Properties.≤-Reasoning._.eqRelation
d_eqRelation_3210 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
d_eqRelation_3210
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_eqRelation_238
-- Data.Nat.Properties.≤-Reasoning._.extractEquality
d_extractEquality_3214 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T_IsEquality_208 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extractEquality_3214 = erased
-- Data.Nat.Properties.≤-Reasoning._.extractStrict
d_extractStrict_3216 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T_IsStrict_172 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_extractStrict_3216 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_extractStrict_198
      v2 v3
-- Data.Nat.Properties.≤-Reasoning._.start
d_start_3224 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_start_3224
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
      (coe d_'8804''45'isPreorder_2810)
      (\ v0 v1 v2 -> coe du_'60''8658''8804'_2854 v2)
-- Data.Nat.Properties.≤-Reasoning._.step-<
d_step'45''60'_3226 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''60'_3226
  = let v0
          = \ v0 v1 v2 v3 v4 -> coe du_'60''45'trans_2980 v1 v3 v4 in
    coe
      (let v1
             = coe
                 MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160 in
       coe
         (let v2
                = \ v2 v3 v4 v5 v6 -> coe du_'60''45''8804''45'trans_2992 v5 v6 in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                  (coe v0) (coe v1) (coe v2)))))
-- Data.Nat.Properties.≤-Reasoning._.step-≡
d_step'45''8801'_3228 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801'_3228
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801'_450
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Nat.Properties.≤-Reasoning._.step-≡-∣
d_step'45''8801''45''8739'_3230 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''8739'_3230 ~v0 ~v1 v2
  = du_step'45''8801''45''8739'_3230 v2
du_step'45''8801''45''8739'_3230 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8801''45''8739'_3230 v0 = coe v0
-- Data.Nat.Properties.≤-Reasoning._.step-≡-⟨
d_step'45''8801''45''10216'_3232 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''10216'_3232
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Nat.Properties.≤-Reasoning._.step-≡-⟩
d_step'45''8801''45''10217'_3234 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''10217'_3234
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Nat.Properties.≤-Reasoning._.step-≡˘
d_step'45''8801''728'_3236 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''728'_3236
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''728'_452
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Nat.Properties.≤-Reasoning._.step-≤
d_step'45''8804'_3238 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8804'_3238
  = let v0 = d_'8804''45'isPreorder_2810 in
    coe
      (let v1
             = \ v1 v2 v3 v4 v5 -> coe du_'8804''45''60''45'trans_2986 v4 v5 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe v0) (coe v1))))
-- Data.Nat.Properties.≤-Reasoning._.stop
d_stop_3240 ::
  Integer ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_stop_3240
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
      (coe d_'8804''45'isPreorder_2810)
-- Data.Nat.Properties.≤-Reasoning._.strictRelation
d_strictRelation_3244 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
d_strictRelation_3244
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202
-- Data.Nat.Properties.≤-Reasoning._.≈-go
d_'8776''45'go_3246 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8776''45'go_3246
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
      (coe d_'8804''45'isPreorder_2810)
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
-- Data.Nat.Properties.≤-Reasoning._.≡-go
d_'8801''45'go_3248 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8801''45'go_3248 ~v0 ~v1 ~v2 ~v3 v4 = du_'8801''45'go_3248 v4
du_'8801''45'go_3248 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_'8801''45'go_3248 v0 = coe v0
-- Data.Nat.Properties.≤-Reasoning._.≤-go
d_'8804''45'go_3250 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8804''45'go_3250
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
      (coe d_'8804''45'isPreorder_2810)
      (\ v0 v1 v2 v3 v4 -> coe du_'8804''45''60''45'trans_2986 v3 v4)
-- Data.Nat.Properties.+-suc
d_'43''45'suc_3272 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'suc_3272 = erased
-- Data.Nat.Properties.+-assoc
d_'43''45'assoc_3280 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'assoc_3280 = erased
-- Data.Nat.Properties.+-identityˡ
d_'43''45'identity'737'_3288 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'identity'737'_3288 = erased
-- Data.Nat.Properties.+-identityʳ
d_'43''45'identity'691'_3290 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'identity'691'_3290 = erased
-- Data.Nat.Properties.+-identity
d_'43''45'identity_3294 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'identity_3294
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.+-comm
d_'43''45'comm_3296 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'comm_3296 = erased
-- Data.Nat.Properties.+-cancelˡ-≡
d_'43''45'cancel'737''45''8801'_3304 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'cancel'737''45''8801'_3304 = erased
-- Data.Nat.Properties.+-cancelʳ-≡
d_'43''45'cancel'691''45''8801'_3312 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'cancel'691''45''8801'_3312 = erased
-- Data.Nat.Properties.+-cancel-≡
d_'43''45'cancel'45''8801'_3314 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'cancel'45''8801'_3314
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.+-isMagma
d_'43''45'isMagma_3316 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'43''45'isMagma_3316
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMagma'46'constructor_1865
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      erased
-- Data.Nat.Properties.+-isSemigroup
d_'43''45'isSemigroup_3318 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'43''45'isSemigroup_3318
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemigroup'46'constructor_10399
      (coe d_'43''45'isMagma_3316) erased
-- Data.Nat.Properties.+-isCommutativeSemigroup
d_'43''45'isCommutativeSemigroup_3320 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548
d_'43''45'isCommutativeSemigroup_3320
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeSemigroup'46'constructor_12071
      (coe d_'43''45'isSemigroup_3318) erased
-- Data.Nat.Properties.+-0-isMonoid
d_'43''45'0'45'isMonoid_3322 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'43''45'0'45'isMonoid_3322
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMonoid'46'constructor_15845
      (coe d_'43''45'isSemigroup_3318) (coe d_'43''45'identity_3294)
-- Data.Nat.Properties.+-0-isCommutativeMonoid
d_'43''45'0'45'isCommutativeMonoid_3324 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'43''45'0'45'isCommutativeMonoid_3324
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeMonoid'46'constructor_17665
      (coe d_'43''45'0'45'isMonoid_3322) erased
-- Data.Nat.Properties.+-magma
d_'43''45'magma_3326 :: MAlonzo.Code.Algebra.Bundles.T_Magma_68
d_'43''45'magma_3326
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Magma'46'constructor_1259 addInt
      d_'43''45'isMagma_3316
-- Data.Nat.Properties.+-semigroup
d_'43''45'semigroup_3328 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_'43''45'semigroup_3328
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Semigroup'46'constructor_9677 addInt
      d_'43''45'isSemigroup_3318
-- Data.Nat.Properties.+-commutativeSemigroup
d_'43''45'commutativeSemigroup_3330 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662
d_'43''45'commutativeSemigroup_3330
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeSemigroup'46'constructor_11895
      addInt d_'43''45'isCommutativeSemigroup_3320
-- Data.Nat.Properties.+-0-monoid
d_'43''45'0'45'monoid_3332 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
d_'43''45'0'45'monoid_3332
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Monoid'46'constructor_15973 addInt
      (0 :: Integer) d_'43''45'0'45'isMonoid_3322
-- Data.Nat.Properties.+-0-commutativeMonoid
d_'43''45'0'45'commutativeMonoid_3334 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962
d_'43''45'0'45'commutativeMonoid_3334
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeMonoid'46'constructor_17727
      addInt (0 :: Integer) d_'43''45'0'45'isCommutativeMonoid_3324
-- Data.Nat.Properties.∸-magma
d_'8760''45'magma_3336 :: MAlonzo.Code.Algebra.Bundles.T_Magma_68
d_'8760''45'magma_3336
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Algebra.du_magma_20
      (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22)
-- Data.Nat.Properties.m≢1+m+n
d_m'8802'1'43'm'43'n_3342 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_m'8802'1'43'm'43'n_3342 = erased
-- Data.Nat.Properties.m≢1+n+m
d_m'8802'1'43'n'43'm_3352 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_m'8802'1'43'n'43'm_3352 = erased
-- Data.Nat.Properties.m+1+n≢m
d_m'43'1'43'n'8802'm_3362 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_m'43'1'43'n'8802'm_3362 = erased
-- Data.Nat.Properties.m+1+n≢n
d_m'43'1'43'n'8802'n_3370 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_m'43'1'43'n'8802'n_3370 = erased
-- Data.Nat.Properties.m+1+n≢0
d_m'43'1'43'n'8802'0_3384 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_m'43'1'43'n'8802'0_3384 = erased
-- Data.Nat.Properties.m+n≡0⇒m≡0
d_m'43'n'8801'0'8658'm'8801'0_3398 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'43'n'8801'0'8658'm'8801'0_3398 = erased
-- Data.Nat.Properties.m+n≡0⇒n≡0
d_m'43'n'8801'0'8658'n'8801'0_3406 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'43'n'8801'0'8658'n'8801'0_3406 = erased
-- Data.Nat.Properties.+-cancelˡ-≤
d_'43''45'cancel'737''45''8804'_3414 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''45'cancel'737''45''8804'_3414 v0 ~v1 ~v2 v3
  = du_'43''45'cancel'737''45''8804'_3414 v0 v3
du_'43''45'cancel'737''45''8804'_3414 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'43''45'cancel'737''45''8804'_3414 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5
                  -> coe du_'43''45'cancel'737''45''8804'_3414 (coe v2) (coe v5)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.+-cancelʳ-≤
d_'43''45'cancel'691''45''8804'_3422 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''45'cancel'691''45''8804'_3422 v0 ~v1 ~v2 v3
  = du_'43''45'cancel'691''45''8804'_3422 v0 v3
du_'43''45'cancel'691''45''8804'_3422 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'43''45'cancel'691''45''8804'_3422 v0 v1
  = coe du_'43''45'cancel'737''45''8804'_3414 (coe v0) (coe v1)
-- Data.Nat.Properties.+-cancel-≤
d_'43''45'cancel'45''8804'_3432 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'cancel'45''8804'_3432
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v0 v1 v2 v3 -> coe du_'43''45'cancel'737''45''8804'_3414 v0 v3)
      (\ v0 v1 v2 v3 -> coe du_'43''45'cancel'691''45''8804'_3422 v0 v3)
-- Data.Nat.Properties.+-cancelˡ-<
d_'43''45'cancel'737''45''60'_3434 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''45'cancel'737''45''60'_3434 v0 ~v1 ~v2 v3
  = du_'43''45'cancel'737''45''60'_3434 v0 v3
du_'43''45'cancel'737''45''60'_3434 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'43''45'cancel'737''45''60'_3434 v0 v1
  = coe du_'43''45'cancel'737''45''8804'_3414 (coe v0) (coe v1)
-- Data.Nat.Properties.+-cancelʳ-<
d_'43''45'cancel'691''45''60'_3444 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''45'cancel'691''45''60'_3444 v0 ~v1 ~v2 v3
  = du_'43''45'cancel'691''45''60'_3444 v0 v3
du_'43''45'cancel'691''45''60'_3444 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'43''45'cancel'691''45''60'_3444 v0 v1
  = coe du_'43''45'cancel'691''45''8804'_3422 (coe v0) (coe v1)
-- Data.Nat.Properties.+-cancel-<
d_'43''45'cancel'45''60'_3454 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'cancel'45''60'_3454
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v0 v1 v2 v3 -> coe du_'43''45'cancel'737''45''60'_3434 v0 v3)
      (\ v0 v1 v2 v3 -> coe du_'43''45'cancel'691''45''60'_3444 v0 v3)
-- Data.Nat.Properties.m≤n⇒m≤o+n
d_m'8804'n'8658'm'8804'o'43'n_3458 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'n'8658'm'8804'o'43'n_3458 ~v0 ~v1 ~v2 v3
  = du_m'8804'n'8658'm'8804'o'43'n_3458 v3
du_m'8804'n'8658'm'8804'o'43'n_3458 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'n'8658'm'8804'o'43'n_3458 v0 = coe v0
-- Data.Nat.Properties.m≤n⇒m≤n+o
d_m'8804'n'8658'm'8804'n'43'o_3468 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'n'8658'm'8804'n'43'o_3468 ~v0 ~v1 ~v2 v3
  = du_m'8804'n'8658'm'8804'n'43'o_3468 v3
du_m'8804'n'8658'm'8804'n'43'o_3468 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'n'8658'm'8804'n'43'o_3468 v0 = coe v0
-- Data.Nat.Properties.m≤m+n
d_m'8804'm'43'n_3482 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'm'43'n_3482 v0 ~v1 = du_m'8804'm'43'n_3482 v0
du_m'8804'm'43'n_3482 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'm'43'n_3482 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (coe du_m'8804'm'43'n_3482 (coe v1)))
-- Data.Nat.Properties.m≤n+m
d_m'8804'n'43'm_3494 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'n'43'm_3494 v0 ~v1 = du_m'8804'n'43'm_3494 v0
du_m'8804'n'43'm_3494 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'n'43'm_3494 v0 = coe du_m'8804'm'43'n_3482 (coe v0)
-- Data.Nat.Properties.m+n≤o⇒m≤o
d_m'43'n'8804'o'8658'm'8804'o_3508 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'43'n'8804'o'8658'm'8804'o_3508 v0 ~v1 ~v2 v3
  = du_m'43'n'8804'o'8658'm'8804'o_3508 v0 v3
du_m'43'n'8804'o'8658'm'8804'o_3508 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'43'n'8804'o'8658'm'8804'o_3508 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5
                  -> coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (coe du_m'43'n'8804'o'8658'm'8804'o_3508 (coe v2) (coe v5))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.m+n≤o⇒n≤o
d_m'43'n'8804'o'8658'n'8804'o_3522 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'43'n'8804'o'8658'n'8804'o_3522 v0 ~v1 ~v2 v3
  = du_m'43'n'8804'o'8658'n'8804'o_3522 v0 v3
du_m'43'n'8804'o'8658'n'8804'o_3522 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'43'n'8804'o'8658'n'8804'o_3522 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                du_m'43'n'8804'o'8658'n'8804'o_3522 (coe v2)
                (coe du_'60''8658''8804'_2854 (coe v1)))
-- Data.Nat.Properties.+-mono-≤
d_'43''45'mono'45''8804'_3530 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''45'mono'45''8804'_3530 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'43''45'mono'45''8804'_3530 v3 v4 v5
du_'43''45'mono'45''8804'_3530 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'43''45'mono'45''8804'_3530 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
        -> coe
             du_'8804''45'trans_2784 (coe v2)
             (coe du_m'8804'n'43'm_3494 (coe v0))
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe du_'43''45'mono'45''8804'_3530 (coe v0) (coe v5) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.+-monoˡ-≤
d_'43''45'mono'737''45''8804'_3544 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''45'mono'737''45''8804'_3544 v0 ~v1 ~v2 v3
  = du_'43''45'mono'737''45''8804'_3544 v0 v3
du_'43''45'mono'737''45''8804'_3544 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'43''45'mono'737''45''8804'_3544 v0 v1
  = coe
      du_'43''45'mono'45''8804'_3530 (coe v0) (coe v1)
      (coe d_'8804''45'refl_2776 (coe v0))
-- Data.Nat.Properties.+-monoʳ-≤
d_'43''45'mono'691''45''8804'_3554 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''45'mono'691''45''8804'_3554 v0 ~v1 v2 v3
  = du_'43''45'mono'691''45''8804'_3554 v0 v2 v3
du_'43''45'mono'691''45''8804'_3554 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'43''45'mono'691''45''8804'_3554 v0 v1 v2
  = coe
      du_'43''45'mono'45''8804'_3530 (coe v1)
      (coe d_'8804''45'refl_2776 (coe v0)) (coe v2)
-- Data.Nat.Properties.+-mono-<-≤
d_'43''45'mono'45''60''45''8804'_3560 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''45'mono'45''60''45''8804'_3560 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'43''45'mono'45''60''45''8804'_3560 v4 v5
du_'43''45'mono'45''60''45''8804'_3560 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'43''45'mono'45''60''45''8804'_3560 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v4
        -> case coe v4 of
             MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
               -> coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v1
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v7
               -> coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (coe
                       du_'43''45'mono'45''60''45''8804'_3560
                       (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v7) (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.+-mono-≤-<
d_'43''45'mono'45''8804''45''60'_3570 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''45'mono'45''8804''45''60'_3570 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'43''45'mono'45''8804''45''60'_3570 v3 v4 v5
du_'43''45'mono'45''8804''45''60'_3570 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'43''45'mono'45''8804''45''60'_3570 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
        -> coe
             du_'8804''45'trans_2784 (coe v2)
             (coe du_m'8804'n'43'm_3494 (coe v0))
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe
                du_'43''45'mono'45''8804''45''60'_3570 (coe v0) (coe v5) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.+-mono-<
d_'43''45'mono'45''60'_3580 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''45'mono'45''60'_3580 ~v0 ~v1 ~v2 v3 v4
  = du_'43''45'mono'45''60'_3580 v3 v4
du_'43''45'mono'45''60'_3580 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'43''45'mono'45''60'_3580 v0 v1
  = coe
      du_'43''45'mono'45''8804''45''60'_3570 (coe v0)
      (coe du_'60''8658''8804'_2854 (coe v1))
-- Data.Nat.Properties.+-monoˡ-<
d_'43''45'mono'737''45''60'_3588 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''45'mono'737''45''60'_3588 v0 ~v1 ~v2
  = du_'43''45'mono'737''45''60'_3588 v0
du_'43''45'mono'737''45''60'_3588 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'43''45'mono'737''45''60'_3588 v0
  = coe du_'43''45'mono'737''45''8804'_3544 (coe v0)
-- Data.Nat.Properties.+-monoʳ-<
d_'43''45'mono'691''45''60'_3596 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'43''45'mono'691''45''60'_3596 v0 ~v1 ~v2 v3
  = du_'43''45'mono'691''45''60'_3596 v0 v3
du_'43''45'mono'691''45''60'_3596 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'43''45'mono'691''45''60'_3596 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (coe du_'43''45'mono'691''45''60'_3596 (coe v2) (coe v1)))
-- Data.Nat.Properties.m+1+n≰m
d_m'43'1'43'n'8816'm_3608 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_m'43'1'43'n'8816'm_3608 = erased
-- Data.Nat.Properties.m<m+n
d_m'60'm'43'n_3618 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'm'43'n_3618 v0 ~v1 v2 = du_m'60'm'43'n_3618 v0 v2
du_m'60'm'43'n_3618 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'm'43'n_3618 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (coe du_m'60'm'43'n_3618 (coe v2) (coe v1)))
-- Data.Nat.Properties.m<n+m
d_m'60'n'43'm_3630 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'43'm_3630 v0 ~v1 v2 = du_m'60'n'43'm_3630 v0 v2
du_m'60'n'43'm_3630 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'n'43'm_3630 v0 v1
  = coe du_m'60'm'43'n_3618 (coe v0) (coe v1)
-- Data.Nat.Properties.m+n≮n
d_m'43'n'8814'n_3646 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_m'43'n'8814'n_3646 = erased
-- Data.Nat.Properties.m+n≮m
d_m'43'n'8814'm_3660 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_m'43'n'8814'm_3660 = erased
-- Data.Nat.Properties.*-suc
d_'42''45'suc_3672 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'suc_3672 = erased
-- Data.Nat.Properties.*-identityˡ
d_'42''45'identity'737'_3684 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'identity'737'_3684 = erased
-- Data.Nat.Properties.*-identityʳ
d_'42''45'identity'691'_3688 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'identity'691'_3688 = erased
-- Data.Nat.Properties.*-identity
d_'42''45'identity_3692 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_3692
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.*-zeroˡ
d_'42''45'zero'737'_3694 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'zero'737'_3694 = erased
-- Data.Nat.Properties.*-zeroʳ
d_'42''45'zero'691'_3696 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'zero'691'_3696 = erased
-- Data.Nat.Properties.*-zero
d_'42''45'zero_3700 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'zero_3700
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.*-comm
d_'42''45'comm_3702 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm_3702 = erased
-- Data.Nat.Properties.*-distribʳ-+
d_'42''45'distrib'691''45''43'_3712 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''43'_3712 = erased
-- Data.Nat.Properties.*-distribˡ-+
d_'42''45'distrib'737''45''43'_3726 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''43'_3726 = erased
-- Data.Nat.Properties.*-distrib-+
d_'42''45'distrib'45''43'_3728 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'distrib'45''43'_3728
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.*-assoc
d_'42''45'assoc_3730 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc_3730 = erased
-- Data.Nat.Properties.*-isMagma
d_'42''45'isMagma_3744 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'42''45'isMagma_3744
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMagma'46'constructor_1865
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      erased
-- Data.Nat.Properties.*-isSemigroup
d_'42''45'isSemigroup_3746 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'42''45'isSemigroup_3746
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemigroup'46'constructor_10399
      (coe d_'42''45'isMagma_3744) erased
-- Data.Nat.Properties.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_3748 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548
d_'42''45'isCommutativeSemigroup_3748
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeSemigroup'46'constructor_12071
      (coe d_'42''45'isSemigroup_3746) erased
-- Data.Nat.Properties.*-1-isMonoid
d_'42''45'1'45'isMonoid_3750 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'42''45'1'45'isMonoid_3750
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMonoid'46'constructor_15845
      (coe d_'42''45'isSemigroup_3746) (coe d_'42''45'identity_3692)
-- Data.Nat.Properties.*-1-isCommutativeMonoid
d_'42''45'1'45'isCommutativeMonoid_3752 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'42''45'1'45'isCommutativeMonoid_3752
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeMonoid'46'constructor_17665
      (coe d_'42''45'1'45'isMonoid_3750) erased
-- Data.Nat.Properties.+-*-isSemiring
d_'43''45''42''45'isSemiring_3754 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570
d_'43''45''42''45'isSemiring_3754
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemiring'46'constructor_47957
      (coe
         MAlonzo.Code.Algebra.Structures.C_IsSemiringWithoutAnnihilatingZero'46'constructor_43717
         (coe d_'43''45'0'45'isCommutativeMonoid_3324) erased erased
         (coe d_'42''45'identity_3692) (coe d_'42''45'distrib'45''43'_3728))
      (coe d_'42''45'zero_3700)
-- Data.Nat.Properties.+-*-isCommutativeSemiring
d_'43''45''42''45'isCommutativeSemiring_3756 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678
d_'43''45''42''45'isCommutativeSemiring_3756
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeSemiring'46'constructor_51779
      (coe d_'43''45''42''45'isSemiring_3754) erased
-- Data.Nat.Properties.*-magma
d_'42''45'magma_3758 :: MAlonzo.Code.Algebra.Bundles.T_Magma_68
d_'42''45'magma_3758
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Magma'46'constructor_1259 mulInt
      d_'42''45'isMagma_3744
-- Data.Nat.Properties.*-semigroup
d_'42''45'semigroup_3760 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_'42''45'semigroup_3760
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Semigroup'46'constructor_9677 mulInt
      d_'42''45'isSemigroup_3746
-- Data.Nat.Properties.*-commutativeSemigroup
d_'42''45'commutativeSemigroup_3762 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662
d_'42''45'commutativeSemigroup_3762
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeSemigroup'46'constructor_11895
      mulInt d_'42''45'isCommutativeSemigroup_3748
-- Data.Nat.Properties.*-1-monoid
d_'42''45'1'45'monoid_3764 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
d_'42''45'1'45'monoid_3764
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Monoid'46'constructor_15973 mulInt
      (1 :: Integer) d_'42''45'1'45'isMonoid_3750
-- Data.Nat.Properties.*-1-commutativeMonoid
d_'42''45'1'45'commutativeMonoid_3766 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962
d_'42''45'1'45'commutativeMonoid_3766
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeMonoid'46'constructor_17727
      mulInt (1 :: Integer) d_'42''45'1'45'isCommutativeMonoid_3752
-- Data.Nat.Properties.+-*-semiring
d_'43''45''42''45'semiring_3768 ::
  MAlonzo.Code.Algebra.Bundles.T_Semiring_2280
d_'43''45''42''45'semiring_3768
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Semiring'46'constructor_41249 addInt
      mulInt (0 :: Integer) (1 :: Integer)
      d_'43''45''42''45'isSemiring_3754
-- Data.Nat.Properties.+-*-commutativeSemiring
d_'43''45''42''45'commutativeSemiring_3770 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2446
d_'43''45''42''45'commutativeSemiring_3770
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeSemiring'46'constructor_44173
      addInt mulInt (0 :: Integer) (1 :: Integer)
      d_'43''45''42''45'isCommutativeSemiring_3756
-- Data.Nat.Properties.*-cancelʳ-≡
d_'42''45'cancel'691''45''8801'_3780 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cancel'691''45''8801'_3780 = erased
-- Data.Nat.Properties.*-cancelˡ-≡
d_'42''45'cancel'737''45''8801'_3802 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'cancel'737''45''8801'_3802 = erased
-- Data.Nat.Properties.m*n≡0⇒m≡0∨n≡0
d_m'42'n'8801'0'8658'm'8801'0'8744'n'8801'0_3822 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_m'42'n'8801'0'8658'm'8801'0'8744'n'8801'0_3822 v0 ~v1 ~v2
  = du_m'42'n'8801'0'8658'm'8801'0'8744'n'8801'0_3822 v0
du_m'42'n'8801'0'8658'm'8801'0'8744'n'8801'0_3822 ::
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_m'42'n'8801'0'8658'm'8801'0'8744'n'8801'0_3822 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      _ -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
-- Data.Nat.Properties.m*n≢0
d_m'42'n'8802'0_3840 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_m'42'n'8802'0_3840 ~v0 ~v1 ~v2 ~v3 = du_m'42'n'8802'0_3840
du_m'42'n'8802'0_3840 :: MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_m'42'n'8802'0_3840
  = coe
      MAlonzo.Code.Data.Nat.Base.C_NonZero'46'constructor_3581
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Nat.Properties.m*n≢0⇒m≢0
d_m'42'n'8802'0'8658'm'8802'0_3850 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_m'42'n'8802'0'8658'm'8802'0_3850 ~v0 ~v1 ~v2
  = du_m'42'n'8802'0'8658'm'8802'0_3850
du_m'42'n'8802'0'8658'm'8802'0_3850 ::
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_m'42'n'8802'0'8658'm'8802'0_3850
  = coe
      MAlonzo.Code.Data.Nat.Base.C_NonZero'46'constructor_3581
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Nat.Properties.m*n≢0⇒n≢0
d_m'42'n'8802'0'8658'n'8802'0_3856 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_m'42'n'8802'0'8658'n'8802'0_3856 ~v0 ~v1 ~v2
  = du_m'42'n'8802'0'8658'n'8802'0_3856
du_m'42'n'8802'0'8658'n'8802'0_3856 ::
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_m'42'n'8802'0'8658'n'8802'0_3856
  = coe du_m'42'n'8802'0'8658'm'8802'0_3850
-- Data.Nat.Properties.m*n≡0⇒m≡0
d_m'42'n'8801'0'8658'm'8801'0_3872 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'42'n'8801'0'8658'm'8801'0_3872 = erased
-- Data.Nat.Properties.m*n≡1⇒m≡1
d_m'42'n'8801'1'8658'm'8801'1_3880 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'42'n'8801'1'8658'm'8801'1_3880 = erased
-- Data.Nat.Properties.m*n≡1⇒n≡1
d_m'42'n'8801'1'8658'n'8801'1_3894 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'42'n'8801'1'8658'n'8801'1_3894 = erased
-- Data.Nat.Properties.[m*n]*[o*p]≡[m*o]*[n*p]
d_'91'm'42'n'93''42''91'o'42'p'93''8801''91'm'42'o'93''42''91'n'42'p'93'_3910 ::
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'91'm'42'n'93''42''91'o'42'p'93''8801''91'm'42'o'93''42''91'n'42'p'93'_3910
  = erased
-- Data.Nat.Properties.m≢0∧n>1⇒m*n>1
d_m'8802'0'8743'n'62'1'8658'm'42'n'62'1_3998 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152 ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152
d_m'8802'0'8743'n'62'1'8658'm'42'n'62'1_3998 ~v0 ~v1 ~v2 ~v3
  = du_m'8802'0'8743'n'62'1'8658'm'42'n'62'1_3998
du_m'8802'0'8743'n'62'1'8658'm'42'n'62'1_3998 ::
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152
du_m'8802'0'8743'n'62'1'8658'm'42'n'62'1_3998
  = coe
      MAlonzo.Code.Data.Nat.Base.C_NonTrivial'46'constructor_5677
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
-- Data.Nat.Properties.n≢0∧m>1⇒m*n>1
d_n'8802'0'8743'm'62'1'8658'm'42'n'62'1_4012 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152 ->
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152
d_n'8802'0'8743'm'62'1'8658'm'42'n'62'1_4012 ~v0 ~v1 ~v2 ~v3
  = du_n'8802'0'8743'm'62'1'8658'm'42'n'62'1_4012
du_n'8802'0'8743'm'62'1'8658'm'42'n'62'1_4012 ::
  MAlonzo.Code.Data.Nat.Base.T_NonTrivial_152
du_n'8802'0'8743'm'62'1'8658'm'42'n'62'1_4012
  = coe du_m'8802'0'8743'n'62'1'8658'm'42'n'62'1_3998
-- Data.Nat.Properties.*-cancelʳ-≤
d_'42''45'cancel'691''45''8804'_4030 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'42''45'cancel'691''45''8804'_4030 v0 ~v1 ~v2 ~v3 ~v4
  = du_'42''45'cancel'691''45''8804'_4030 v0
du_'42''45'cancel'691''45''8804'_4030 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'42''45'cancel'691''45''8804'_4030 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (coe du_'42''45'cancel'691''45''8804'_4030 (coe v1)))
-- Data.Nat.Properties.*-cancelˡ-≤
d_'42''45'cancel'737''45''8804'_4044 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'42''45'cancel'737''45''8804'_4044 v0 ~v1 ~v2 ~v3
  = du_'42''45'cancel'737''45''8804'_4044 v0
du_'42''45'cancel'737''45''8804'_4044 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'42''45'cancel'737''45''8804'_4044 v0 v1
  = coe du_'42''45'cancel'691''45''8804'_4030 (coe v0)
-- Data.Nat.Properties.*-mono-≤
d_'42''45'mono'45''8804'_4060 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'42''45'mono'45''8804'_4060 ~v0 v1 ~v2 v3 v4 v5
  = du_'42''45'mono'45''8804'_4060 v1 v3 v4 v5
du_'42''45'mono'45''8804'_4060 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'42''45'mono'45''8804'_4060 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
        -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
        -> let v7 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                du_'43''45'mono'45''8804'_3530 (coe mulInt (coe v7) (coe v1))
                (coe v3)
                (coe
                   du_'42''45'mono'45''8804'_4060 (coe v7) (coe v1) (coe v6)
                   (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.*-monoˡ-≤
d_'42''45'mono'737''45''8804'_4070 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'42''45'mono'737''45''8804'_4070 v0 ~v1 v2 v3
  = du_'42''45'mono'737''45''8804'_4070 v0 v2 v3
du_'42''45'mono'737''45''8804'_4070 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'42''45'mono'737''45''8804'_4070 v0 v1 v2
  = coe
      du_'42''45'mono'45''8804'_4060 (coe v1) (coe v0) (coe v2)
      (coe d_'8804''45'refl_2776 (coe v0))
-- Data.Nat.Properties.*-monoʳ-≤
d_'42''45'mono'691''45''8804'_4080 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'42''45'mono'691''45''8804'_4080 v0 ~v1 v2 v3
  = du_'42''45'mono'691''45''8804'_4080 v0 v2 v3
du_'42''45'mono'691''45''8804'_4080 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'42''45'mono'691''45''8804'_4080 v0 v1 v2
  = coe
      du_'42''45'mono'45''8804'_4060 (coe v0) (coe v1)
      (coe d_'8804''45'refl_2776 (coe v0)) (coe v2)
-- Data.Nat.Properties.*-mono-<
d_'42''45'mono'45''60'_4086 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'42''45'mono'45''60'_4086 ~v0 v1 ~v2 v3 v4 v5
  = du_'42''45'mono'45''60'_4086 v1 v3 v4 v5
du_'42''45'mono'45''60'_4086 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'42''45'mono'45''60'_4086 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
        -> case coe v6 of
             MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
               -> coe seq (coe v3) (coe du_0'60'1'43'n_3074)
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9
               -> case coe v3 of
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v12
                      -> coe
                           du_'43''45'mono'45''60'_3580
                           (mulInt (coe subInt (coe v0) (coe (1 :: Integer))) (coe v1))
                           (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v12)
                           (coe
                              du_'42''45'mono'45''60'_4086
                              (coe subInt (coe v0) (coe (1 :: Integer))) (coe v1)
                              (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9)
                              (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.*-monoˡ-<
d_'42''45'mono'737''45''60'_4100 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'42''45'mono'737''45''60'_4100 v0 ~v1 v2 v3 v4
  = du_'42''45'mono'737''45''60'_4100 v0 v2 v3 v4
du_'42''45'mono'737''45''60'_4100 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'42''45'mono'737''45''60'_4100 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
        -> case coe v6 of
             MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26 -> coe du_0'60'1'43'n_3074
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9
               -> let v10 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    (coe
                       du_'43''45'mono'45''8804''45''60'_3570
                       (coe
                          MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                          (\ v11 v12 -> v12) (\ v11 -> mulInt (coe v11) (coe v0)) v10
                          (subInt (coe v2) (coe (1 :: Integer))))
                       (coe d_'8804''45'refl_2776 (coe v0))
                       (coe
                          du_'42''45'mono'737''45''60'_4100 (coe v0) (coe v10)
                          (coe subInt (coe v2) (coe (1 :: Integer)))
                          (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.*-monoʳ-<
d_'42''45'mono'691''45''60'_4114 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'42''45'mono'691''45''60'_4114 v0 ~v1 ~v2 v3 v4
  = du_'42''45'mono'691''45''60'_4114 v0 v3 v4
du_'42''45'mono'691''45''60'_4114 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'42''45'mono'691''45''60'_4114 v0 v1 v2
  = case coe v0 of
      1 -> case coe v2 of
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5
               -> coe
                    du_'43''45'mono'45''8804'_3530 (coe (0 :: Integer))
                    (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5)
                    (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> case coe v2 of
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5
               -> coe
                    du_'43''45'mono'45''8804'_3530
                    (coe mulInt (coe subInt (coe v0) (coe (1 :: Integer))) (coe v1))
                    (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5)
                    (coe
                       du_'60''8658''8804'_2854
                       (coe
                          du_'42''45'mono'691''45''60'_4114
                          (coe subInt (coe v0) (coe (1 :: Integer))) (coe v1)
                          (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.m≤m*n
d_m'8804'm'42'n_4128 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'm'42'n_4128 v0 v1 ~v2 = du_m'8804'm'42'n_4128 v0 v1
du_m'8804'm'42'n_4128 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'm'42'n_4128 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_2810)
         (\ v2 v3 v4 -> coe du_'60''8658''8804'_2854 v4))
      v0 (mulInt (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
         (\ v2 v3 v4 v5 v6 -> v6) v0 (mulInt (coe v0) (coe (1 :: Integer)))
         (mulInt (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe d_'8804''45'isPreorder_2810)
               (\ v2 v3 v4 v5 v6 -> coe du_'8804''45''60''45'trans_2986 v5 v6))
            (mulInt (coe v0) (coe (1 :: Integer))) (mulInt (coe v0) (coe v1))
            (mulInt (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe d_'8804''45'isPreorder_2810))
               (coe mulInt (coe v0) (coe v1)))
            (coe
               du_'42''45'mono'691''45''8804'_4080 (coe v0) (coe v1)
               (coe du_0'60'1'43'n_3074)))
         erased)
-- Data.Nat.Properties.m≤n*m
d_m'8804'n'42'm_4140 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'n'42'm_4140 v0 v1 ~v2 = du_m'8804'n'42'm_4140 v0 v1
du_m'8804'n'42'm_4140 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'n'42'm_4140 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_2810)
         (\ v2 v3 v4 -> coe du_'60''8658''8804'_2854 v4))
      v0 (mulInt (coe v1) (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
            (coe d_'8804''45'isPreorder_2810)
            (\ v2 v3 v4 v5 v6 -> coe du_'8804''45''60''45'trans_2986 v5 v6))
         v0 (mulInt (coe v0) (coe v1)) (mulInt (coe v1) (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
            (\ v2 v3 v4 v5 v6 -> v6) (mulInt (coe v0) (coe v1))
            (mulInt (coe v1) (coe v0)) (mulInt (coe v1) (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe d_'8804''45'isPreorder_2810))
               (coe mulInt (coe v1) (coe v0)))
            erased)
         (coe du_m'8804'm'42'n_4128 (coe v0) (coe v1)))
-- Data.Nat.Properties.m<m*n
d_m'60'm'42'n_4152 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'm'42'n_4152 v0 v1 ~v2 v3 = du_m'60'm'42'n_4152 v0 v1 v3
du_m'60'm'42'n_4152 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'm'42'n_4152 v0 v1 v2
  = let v3 = subInt (coe v0) (coe (1 :: Integer)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
           -> coe
                seq (coe v6)
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202)
                   (coe v0) (coe mulInt (coe v0) (coe v1))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                         (\ v7 v8 v9 v10 v11 -> coe du_'60''45'trans_2980 v8 v10 v11)
                         (coe
                            MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                         (\ v7 v8 v9 v10 v11 ->
                            coe du_'60''45''8804''45'trans_2992 v10 v11))
                      v0 (addInt (coe v1) (coe v3)) (mulInt (coe v0) (coe v1))
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                            (coe d_'8804''45'isPreorder_2810)
                            (\ v7 v8 v9 v10 v11 ->
                               coe du_'8804''45''60''45'trans_2986 v10 v11))
                         (addInt (coe v1) (coe v3))
                         (addInt (coe v1) (coe mulInt (coe v3) (coe v1)))
                         (mulInt (coe v0) (coe v1))
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                               (coe d_'8804''45'isPreorder_2810))
                            (coe mulInt (coe v0) (coe v1)))
                         (coe
                            du_'43''45'mono'691''45''8804'_3554 (coe v1)
                            (coe mulInt (coe v3) (coe v1))
                            (coe du_m'8804'm'42'n_4128 (coe v3) (coe v1))))
                      (coe
                         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                         (coe
                            MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                            (coe du_m'8804'n'43'm_3494 (coe v3))))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.m<n⇒m<n*o
d_m'60'n'8658'm'60'n'42'o_4166 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'8658'm'60'n'42'o_4166 ~v0 v1 v2 ~v3 v4
  = du_m'60'n'8658'm'60'n'42'o_4166 v1 v2 v4
du_m'60'n'8658'm'60'n'42'o_4166 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'n'8658'm'60'n'42'o_4166 v0 v1 v2
  = coe
      du_'60''45''8804''45'trans_2992 (coe v2)
      (coe du_m'8804'm'42'n_4128 (coe v0) (coe v1))
-- Data.Nat.Properties.m<n⇒m<o*n
d_m'60'n'8658'm'60'o'42'n_4182 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'8658'm'60'o'42'n_4182 v0 v1 v2 ~v3 v4
  = du_m'60'n'8658'm'60'o'42'n_4182 v0 v1 v2 v4
du_m'60'n'8658'm'60'o'42'n_4182 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'n'8658'm'60'o'42'n_4182 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
         (coe v4) (coe v0) (coe mulInt (coe v2) (coe v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
               (\ v5 v6 v7 v8 v9 -> coe du_'60''45'trans_2980 v6 v8 v9)
               (coe
                  MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
               (\ v5 v6 v7 v8 v9 -> coe du_'60''45''8804''45'trans_2992 v8 v9))
            v0 (mulInt (coe v1) (coe v2)) (mulInt (coe v2) (coe v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
               (\ v5 v6 v7 v8 v9 -> v9) (mulInt (coe v1) (coe v2))
               (mulInt (coe v2) (coe v1)) (mulInt (coe v2) (coe v1))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                     (coe d_'8804''45'isPreorder_2810))
                  (coe mulInt (coe v2) (coe v1)))
               erased)
            (coe du_m'60'n'8658'm'60'n'42'o_4166 (coe v1) (coe v2) (coe v3))))
-- Data.Nat.Properties.*-cancelʳ-<
d_'42''45'cancel'691''45''60'_4192 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'42''45'cancel'691''45''60'_4192 v0 v1 v2 ~v3
  = du_'42''45'cancel'691''45''60'_4192 v0 v1 v2
du_'42''45'cancel'691''45''60'_4192 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'42''45'cancel'691''45''60'_4192 v0 v1 v2
  = let v3
          = let v3 = subInt (coe v1) (coe (1 :: Integer)) in
            coe
              (let v4 = subInt (coe v2) (coe (1 :: Integer)) in
               coe
                 (coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (coe
                       du_'42''45'cancel'691''45''60'_4192 (coe v0) (coe v3)
                       (coe v4)))) in
    coe
      (coe
         seq (coe v0)
         (case coe v1 of
            0 -> case coe v2 of
                   _ | coe geqInt (coe v2) (coe (1 :: Integer)) ->
                       coe du_0'60'1'43'n_3074
                   _ -> coe v3
            _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                 coe
                   (case coe v2 of
                      _ | coe geqInt (coe v2) (coe (1 :: Integer)) ->
                          let v5 = subInt (coe v2) (coe (1 :: Integer)) in
                          coe
                            (coe
                               MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                               (coe
                                  du_'42''45'cancel'691''45''60'_4192 (coe v0) (coe v4) (coe v5)))
                      _ -> coe v3)))
-- Data.Nat.Properties.*-cancelˡ-<
d_'42''45'cancel'737''45''60'_4208 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'42''45'cancel'737''45''60'_4208 v0 v1 v2 v3
  = coe
      du_'42''45'cancel'691''45''60'_4192 (coe v0) (coe v1) (coe v2)
-- Data.Nat.Properties.*-cancel-<
d_'42''45'cancel'45''60'_4224 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'cancel'45''60'_4224
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_'42''45'cancel'737''45''60'_4208)
      (\ v0 v1 v2 v3 -> coe du_'42''45'cancel'691''45''60'_4192 v0 v1 v2)
-- Data.Nat.Properties.^-identityʳ
d_'94''45'identity'691'_4226 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'94''45'identity'691'_4226 = erased
-- Data.Nat.Properties.^-zeroˡ
d_'94''45'zero'737'_4230 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'94''45'zero'737'_4230 = erased
-- Data.Nat.Properties.^-distribˡ-+-*
d_'94''45'distrib'737''45''43''45''42'_4240 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'94''45'distrib'737''45''43''45''42'_4240 = erased
-- Data.Nat.Properties.^-semigroup-morphism
d_'94''45'semigroup'45'morphism_4258 ::
  Integer -> MAlonzo.Code.Algebra.Morphism.T_IsSemigroupMorphism_148
d_'94''45'semigroup'45'morphism_4258 ~v0
  = du_'94''45'semigroup'45'morphism_4258
du_'94''45'semigroup'45'morphism_4258 ::
  MAlonzo.Code.Algebra.Morphism.T_IsSemigroupMorphism_148
du_'94''45'semigroup'45'morphism_4258
  = coe
      MAlonzo.Code.Algebra.Morphism.C_IsSemigroupMorphism'46'constructor_1081
      erased erased
-- Data.Nat.Properties.^-monoid-morphism
d_'94''45'monoid'45'morphism_4266 ::
  Integer -> MAlonzo.Code.Algebra.Morphism.T_IsMonoidMorphism_306
d_'94''45'monoid'45'morphism_4266 ~v0
  = du_'94''45'monoid'45'morphism_4266
du_'94''45'monoid'45'morphism_4266 ::
  MAlonzo.Code.Algebra.Morphism.T_IsMonoidMorphism_306
du_'94''45'monoid'45'morphism_4266
  = coe
      MAlonzo.Code.Algebra.Morphism.C_IsMonoidMorphism'46'constructor_2137
      (coe du_'94''45'semigroup'45'morphism_4258) erased
-- Data.Nat.Properties.^-*-assoc
d_'94''45''42''45'assoc_4274 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'94''45''42''45'assoc_4274 = erased
-- Data.Nat.Properties.m^n≡0⇒m≡0
d_m'94'n'8801'0'8658'm'8801'0_4296 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'94'n'8801'0'8658'm'8801'0_4296 = erased
-- Data.Nat.Properties.m^n≡1⇒n≡0∨m≡1
d_m'94'n'8801'1'8658'n'8801'0'8744'm'8801'1_4308 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_m'94'n'8801'1'8658'n'8801'0'8744'm'8801'1_4308 ~v0 v1 ~v2
  = du_m'94'n'8801'1'8658'n'8801'0'8744'm'8801'1_4308 v1
du_m'94'n'8801'1'8658'n'8801'0'8744'm'8801'1_4308 ::
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_m'94'n'8801'1'8658'n'8801'0'8744'm'8801'1_4308 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
      _ -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
-- Data.Nat.Properties.m^n≢0
d_m'94'n'8802'0_4324 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_m'94'n'8802'0_4324 v0 v1 ~v2 = du_m'94'n'8802'0_4324 v0 v1
du_m'94'n'8802'0_4324 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_m'94'n'8802'0_4324 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Base.du_'8802''45'nonZero_126
      (coe MAlonzo.Code.Data.Nat.Base.d__'94'__272 (coe v0) (coe v1))
-- Data.Nat.Properties.m^n>0
d_m'94'n'62'0_4336 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'94'n'62'0_4336 ~v0 ~v1 ~v2 = du_m'94'n'62'0_4336
du_m'94'n'62'0_4336 :: MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'94'n'62'0_4336
  = coe MAlonzo.Code.Data.Nat.Base.du_'62''45'nonZero'8315''185'_146
-- Data.Nat.Properties.^-monoˡ-≤
d_'94''45'mono'737''45''8804'_4346 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'94''45'mono'737''45''8804'_4346 v0 ~v1 v2 v3
  = du_'94''45'mono'737''45''8804'_4346 v0 v2 v3
du_'94''45'mono'737''45''8804'_4346 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'94''45'mono'737''45''8804'_4346 v0 v1 v2
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                du_'42''45'mono'45''8804'_4060 (coe v1)
                (coe MAlonzo.Code.Data.Nat.Base.d__'94'__272 (coe v1) (coe v3))
                (coe v2)
                (coe
                   du_'94''45'mono'737''45''8804'_4346 (coe v3) (coe v1) (coe v2)))
-- Data.Nat.Properties.^-monoʳ-≤
d_'94''45'mono'691''45''8804'_4360 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'94''45'mono'691''45''8804'_4360 v0 ~v1 v2 v3 v4
  = du_'94''45'mono'691''45''8804'_4360 v0 v2 v3 v4
du_'94''45'mono'691''45''8804'_4360 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'94''45'mono'691''45''8804'_4360 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
        -> coe
             du_n'8802'0'8658'n'62'0_3090
             (coe MAlonzo.Code.Data.Nat.Base.d__'94'__272 (coe v0) (coe v2))
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
        -> let v7 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v8 = subInt (coe v2) (coe (1 :: Integer)) in
              coe
                (coe
                   du_'42''45'mono'691''45''8804'_4080 (coe v0)
                   (coe
                      MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                      (\ v9 v10 -> v10)
                      (MAlonzo.Code.Data.Nat.Base.d__'94'__272 (coe v0)) v7 v8)
                   (coe
                      du_'94''45'mono'691''45''8804'_4360 (coe v0) (coe v7) (coe v8)
                      (coe v6))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.^-monoˡ-<
d_'94''45'mono'737''45''60'_4376 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'94''45'mono'737''45''60'_4376 v0 ~v1 v2 v3 v4
  = du_'94''45'mono'737''45''60'_4376 v0 v2 v3 v4
du_'94''45'mono'737''45''60'_4376 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'94''45'mono'737''45''60'_4376 v0 v1 v2 v3
  = case coe v0 of
      1 -> coe
             du_'42''45'mono'737''45''60'_4100 (coe (1 :: Integer)) (coe v1)
             (coe v2) (coe v3)
      _ -> coe
             du_'42''45'mono'45''60'_4086 (coe v2)
             (coe
                MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                (\ v4 v5 -> v5)
                (\ v4 ->
                   MAlonzo.Code.Data.Nat.Base.d__'94'__272
                     (coe v4) (coe subInt (coe v0) (coe (1 :: Integer))))
                v1 v2)
             (coe v3)
             (coe
                du_'94''45'mono'737''45''60'_4376
                (coe subInt (coe v0) (coe (1 :: Integer))) (coe v1) (coe v2)
                (coe v3))
-- Data.Nat.Properties.^-monoʳ-<
d_'94''45'mono'691''45''60'_4388 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'94''45'mono'691''45''60'_4388 v0 v1 v2 v3 v4
  = case coe v2 of
      0 -> let v5 = subInt (coe v3) (coe (1 :: Integer)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v8
                  -> coe
                       seq (coe v8)
                       (coe
                          du_'42''45'mono'45''8804'_4060 (coe v0)
                          (coe MAlonzo.Code.Data.Nat.Base.d__'94'__272 (coe v0) (coe v5))
                          (coe v1) (coe du_m'94'n'62'0_4336))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> let v5 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (let v6 = subInt (coe v3) (coe (1 :: Integer)) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9
                     -> coe
                          du_'42''45'mono'691''45''60'_4114 (coe v0)
                          (coe
                             MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                             (\ v10 v11 -> v11)
                             (MAlonzo.Code.Data.Nat.Base.d__'94'__272 (coe v0)) v5 v6)
                          (coe
                             d_'94''45'mono'691''45''60'_4388 (coe v0) (coe v1) (coe v5)
                             (coe v6) (coe v9))
                   _ -> MAlonzo.RTE.mazUnreachableError))
-- Data.Nat.Properties.m≤n⇒m⊔n≡n
d_m'8804'n'8658'm'8852'n'8801'n_4406 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8804'n'8658'm'8852'n'8801'n_4406 = erased
-- Data.Nat.Properties.m≥n⇒m⊔n≡m
d_m'8805'n'8658'm'8852'n'8801'm_4412 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8805'n'8658'm'8852'n'8801'm_4412 = erased
-- Data.Nat.Properties.m≤n⇒m⊓n≡m
d_m'8804'n'8658'm'8851'n'8801'm_4422 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8804'n'8658'm'8851'n'8801'm_4422 = erased
-- Data.Nat.Properties.m≥n⇒m⊓n≡n
d_m'8805'n'8658'm'8851'n'8801'n_4428 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8805'n'8658'm'8851'n'8801'n_4428 = erased
-- Data.Nat.Properties.⊓-operator
d_'8851''45'operator_4438 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98
d_'8851''45'operator_4438
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.C_MinOperator'46'constructor_1121
      (coe MAlonzo.Code.Data.Nat.Base.d__'8851'__232) erased erased
-- Data.Nat.Properties.⊔-operator
d_'8852''45'operator_4440 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_128
d_'8852''45'operator_4440
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.C_MaxOperator'46'constructor_1659
      (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__204) erased erased
-- Data.Nat.Properties.⊔≡⊔′
d_'8852''8801''8852''8242'_4446 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852''8801''8852''8242'_4446 = erased
-- Data.Nat.Properties.⊓≡⊓′
d_'8851''8801''8851''8242'_4472 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''8801''8851''8242'_4472 = erased
-- Data.Nat.Properties.⊓-⊔-properties.antimono-≤-distrib-⊓
d_antimono'45''8804''45'distrib'45''8851'_4496 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antimono'45''8804''45'distrib'45''8851'_4496 = erased
-- Data.Nat.Properties.⊓-⊔-properties.antimono-≤-distrib-⊔
d_antimono'45''8804''45'distrib'45''8852'_4498 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antimono'45''8804''45'distrib'45''8852'_4498 = erased
-- Data.Nat.Properties.⊓-⊔-properties.mono-≤-distrib-⊓
d_mono'45''8804''45'distrib'45''8851'_4500 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono'45''8804''45'distrib'45''8851'_4500 = erased
-- Data.Nat.Properties.⊓-⊔-properties.mono-≤-distrib-⊔
d_mono'45''8804''45'distrib'45''8852'_4502 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono'45''8804''45'distrib'45''8852'_4502 = erased
-- Data.Nat.Properties.⊓-⊔-properties.x⊓y≤x
d_x'8851'y'8804'x_4504 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8851'y'8804'x_4504
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2808
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.x≤y⇒x⊓z≤y
d_x'8804'y'8658'x'8851'z'8804'y_4506 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8804'y'8658'x'8851'z'8804'y_4506
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'x'8851'z'8804'y_3160
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.x≤y⇒z⊓x≤y
d_x'8804'y'8658'z'8851'x'8804'y_4508 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8804'y'8658'z'8851'x'8804'y_4508
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'z'8851'x'8804'y_3172
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.x≤y⇒x⊓z≤y
d_x'8804'y'8658'x'8851'z'8804'y_4510 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8804'y'8658'x'8851'z'8804'y_4510
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'x'8851'z'8804'y_3160
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.x≤y⇒z⊓x≤y
d_x'8804'y'8658'z'8851'x'8804'y_4512 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8804'y'8658'z'8851'x'8804'y_4512
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'z'8851'x'8804'y_3172
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.x≤y⊓z⇒x≤y
d_x'8804'y'8851'z'8658'x'8804'y_4514 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8804'y'8851'z'8658'x'8804'y_4514
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'y_3184
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.x≤y⊓z⇒x≤z
d_x'8804'y'8851'z'8658'x'8804'z_4516 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8804'y'8851'z'8658'x'8804'z_4516
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'z_3198
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.x⊓y≤y
d_x'8851'y'8804'y_4518 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8851'y'8804'y_4518
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2834
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.x⊓y≈x⇒x≤y
d_x'8851'y'8776'x'8658'x'8804'y_4520 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8851'y'8776'x'8658'x'8804'y_4520
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3068
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.x⊓y≈y⇒y≤x
d_x'8851'y'8776'y'8658'y'8804'x_4522 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8851'y'8776'y'8658'y'8804'x_4522
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3100
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.x⊓y≤x
d_x'8851'y'8804'x_4524 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8851'y'8804'x_4524
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2808
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.x⊓y≤x⊔y
d_x'8851'y'8804'x'8852'y_4526 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8851'y'8804'x'8852'y_4526
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_x'8851'y'8804'x'8852'y_3318
      (coe d_'8804''45'totalPreorder_2822)
      (coe d_'8851''45'operator_4438) (coe d_'8852''45'operator_4440)
-- Data.Nat.Properties.⊓-⊔-properties.x⊓y≤y
d_x'8851'y'8804'y_4528 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8851'y'8804'y_4528
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2834
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.x⊓y≈x⇒x≤y
d_x'8851'y'8776'x'8658'x'8804'y_4530 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8851'y'8776'x'8658'x'8804'y_4530
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3068
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.x⊓y≈y⇒y≤x
d_x'8851'y'8776'y'8658'y'8804'x_4532 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8851'y'8776'y'8658'y'8804'x_4532
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3100
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.x≤y⊓z⇒x≤y
d_x'8804'y'8851'z'8658'x'8804'y_4534 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8804'y'8851'z'8658'x'8804'y_4534
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'y_3184
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.x≤y⊓z⇒x≤z
d_x'8804'y'8851'z'8658'x'8804'z_4536 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_x'8804'y'8851'z'8658'x'8804'z_4536
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'z_3198
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-absorbs-⊔
d_'8851''45'absorbs'45''8852'_4538 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'absorbs'45''8852'_4538 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-assoc
d_'8851''45'assoc_4540 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'assoc_4540 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-band
d_'8851''45'band_4542 :: MAlonzo.Code.Algebra.Bundles.T_Band_596
d_'8851''45'band_4542
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'band_3052
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-comm
d_'8851''45'comm_4544 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'comm_4544 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-commutativeSemigroup
d_'8851''45'commutativeSemigroup_4546 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662
d_'8851''45'commutativeSemigroup_4546
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'commutativeSemigroup_3054
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-distrib-⊔
d_'8851''45'distrib'45''8852'_4554 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'distrib'45''8852'_4554
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8851''45'distrib'45''8852'_3138
      (coe d_'8804''45'totalPreorder_2822)
      (coe d_'8851''45'operator_4438) (coe d_'8852''45'operator_4440)
-- Data.Nat.Properties.⊓-⊔-properties.⊓-distribʳ-⊔
d_'8851''45'distrib'691''45''8852'_4556 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'distrib'691''45''8852'_4556 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-distribˡ-⊔
d_'8851''45'distrib'737''45''8852'_4558 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'distrib'737''45''8852'_4558 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-glb
d_'8851''45'glb_4560 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8851''45'glb_4560
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3278
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-idem
d_'8851''45'idem_4562 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'idem_4562 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-isBand
d_'8851''45'isBand_4570 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_'8851''45'isBand_4570
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isBand_3034
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-isCommutativeSemigroup
d_'8851''45'isCommutativeSemigroup_4572 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548
d_'8851''45'isCommutativeSemigroup_4572
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isCommutativeSemigroup_3036
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-isMagma
d_'8851''45'isMagma_4574 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'8851''45'isMagma_4574
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMagma_3030
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-isSelectiveMagma
d_'8851''45'isSelectiveMagma_4578 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_436
d_'8851''45'isSelectiveMagma_4578
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3038
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-isSemigroup
d_'8851''45'isSemigroup_4580 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'8851''45'isSemigroup_4580
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSemigroup_3032
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-magma
d_'8851''45'magma_4582 :: MAlonzo.Code.Algebra.Bundles.T_Magma_68
d_'8851''45'magma_4582
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'magma_3048
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-mono-≤
d_'8851''45'mono'45''8804'_4584 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8851''45'mono'45''8804'_4584
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'45''8804'_3206
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-monoʳ-≤
d_'8851''45'mono'691''45''8804'_4588 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8851''45'mono'691''45''8804'_4588
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3266
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-monoˡ-≤
d_'8851''45'mono'737''45''8804'_4590 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8851''45'mono'737''45''8804'_4590
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'737''45''8804'_3256
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-sel
d_'8851''45'sel_4594 ::
  Integer -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8851''45'sel_4594
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'sel_2988
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-selectiveMagma
d_'8851''45'selectiveMagma_4596 ::
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_122
d_'8851''45'selectiveMagma_4596
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'selectiveMagma_3056
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-semigroup
d_'8851''45'semigroup_4598 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_'8851''45'semigroup_4598
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'semigroup_3050
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-triangulate
d_'8851''45'triangulate_4600 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'triangulate_4600 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-⊔-absorptive
d_'8851''45''8852''45'absorptive_4608 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45''8852''45'absorptive_4608
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'absorptive_3218
      (coe d_'8804''45'totalPreorder_2822)
      (coe d_'8851''45'operator_4438) (coe d_'8852''45'operator_4440)
-- Data.Nat.Properties.⊓-⊔-properties.⊔-absorbs-⊓
d_'8852''45'absorbs'45''8851'_4610 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852''45'absorbs'45''8851'_4610 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-assoc
d_'8851''45'assoc_4612 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'assoc_4612 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-band
d_'8851''45'band_4614 :: MAlonzo.Code.Algebra.Bundles.T_Band_596
d_'8851''45'band_4614
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'band_3052
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-comm
d_'8851''45'comm_4616 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'comm_4616 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-commutativeSemigroup
d_'8851''45'commutativeSemigroup_4618 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_662
d_'8851''45'commutativeSemigroup_4618
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'commutativeSemigroup_3054
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊔-distrib-⊓
d_'8852''45'distrib'45''8851'_4626 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8852''45'distrib'45''8851'_4626
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8852''45'distrib'45''8851'_3170
      (coe d_'8804''45'totalPreorder_2822)
      (coe d_'8851''45'operator_4438) (coe d_'8852''45'operator_4440)
-- Data.Nat.Properties.⊓-⊔-properties.⊔-distribʳ-⊓
d_'8852''45'distrib'691''45''8851'_4628 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852''45'distrib'691''45''8851'_4628 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊔-distribˡ-⊓
d_'8852''45'distrib'737''45''8851'_4630 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852''45'distrib'737''45''8851'_4630 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-idem
d_'8851''45'idem_4632 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'idem_4632 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊓-isBand
d_'8851''45'isBand_4640 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_'8851''45'isBand_4640
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isBand_3034
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-isCommutativeSemigroup
d_'8851''45'isCommutativeSemigroup_4642 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548
d_'8851''45'isCommutativeSemigroup_4642
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isCommutativeSemigroup_3036
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-isMagma
d_'8851''45'isMagma_4644 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'8851''45'isMagma_4644
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMagma_3030
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-isSelectiveMagma
d_'8851''45'isSelectiveMagma_4648 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_436
d_'8851''45'isSelectiveMagma_4648
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3038
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-isSemigroup
d_'8851''45'isSemigroup_4650 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'8851''45'isSemigroup_4650
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSemigroup_3032
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-glb
d_'8851''45'glb_4652 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8851''45'glb_4652
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3278
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-magma
d_'8851''45'magma_4654 :: MAlonzo.Code.Algebra.Bundles.T_Magma_68
d_'8851''45'magma_4654
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'magma_3048
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-mono-≤
d_'8851''45'mono'45''8804'_4656 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8851''45'mono'45''8804'_4656
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'45''8804'_3206
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-monoʳ-≤
d_'8851''45'mono'691''45''8804'_4660 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8851''45'mono'691''45''8804'_4660
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3266
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-monoˡ-≤
d_'8851''45'mono'737''45''8804'_4662 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8851''45'mono'737''45''8804'_4662
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'737''45''8804'_3256
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-sel
d_'8851''45'sel_4664 ::
  Integer -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8851''45'sel_4664
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'sel_2988
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-selectiveMagma
d_'8851''45'selectiveMagma_4666 ::
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_122
d_'8851''45'selectiveMagma_4666
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'selectiveMagma_3056
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-semigroup
d_'8851''45'semigroup_4668 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_'8851''45'semigroup_4668
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'semigroup_3050
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-properties.⊓-triangulate
d_'8851''45'triangulate_4670 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'triangulate_4670 = erased
-- Data.Nat.Properties.⊓-⊔-properties.⊔-⊓-absorptive
d_'8852''45''8851''45'absorptive_4678 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8852''45''8851''45'absorptive_4678
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'absorptive_3216
      (coe d_'8804''45'totalPreorder_2822)
      (coe d_'8851''45'operator_4438) (coe d_'8852''45'operator_4440)
-- Data.Nat.Properties.⊓-⊔-latticeProperties.⊓-isSemilattice
d_'8851''45'isSemilattice_4682 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
d_'8851''45'isSemilattice_4682
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'isSemilattice_602
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-latticeProperties.⊓-semilattice
d_'8851''45'semilattice_4684 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8851''45'semilattice_4684
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'semilattice_604
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊓-⊔-latticeProperties.⊓-⊔-distributiveLattice
d_'8851''45''8852''45'distributiveLattice_4686 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584
d_'8851''45''8852''45'distributiveLattice_4686
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'distributiveLattice_808
      (coe d_'8804''45'totalPreorder_2822)
      (coe d_'8851''45'operator_4438) (coe d_'8852''45'operator_4440)
-- Data.Nat.Properties.⊓-⊔-latticeProperties.⊓-⊔-isDistributiveLattice
d_'8851''45''8852''45'isDistributiveLattice_4688 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036
d_'8851''45''8852''45'isDistributiveLattice_4688
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'isDistributiveLattice_798
      (coe d_'8804''45'totalPreorder_2822)
      (coe d_'8851''45'operator_4438) (coe d_'8852''45'operator_4440)
-- Data.Nat.Properties.⊓-⊔-latticeProperties.⊓-⊔-isLattice
d_'8851''45''8852''45'isLattice_4690 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962
d_'8851''45''8852''45'isLattice_4690
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'isLattice_796
      (coe d_'8804''45'totalPreorder_2822)
      (coe d_'8851''45'operator_4438) (coe d_'8852''45'operator_4440)
-- Data.Nat.Properties.⊓-⊔-latticeProperties.⊓-⊔-lattice
d_'8851''45''8852''45'lattice_4692 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500
d_'8851''45''8852''45'lattice_4692
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'lattice_804
      (coe d_'8804''45'totalPreorder_2822)
      (coe d_'8851''45'operator_4438) (coe d_'8852''45'operator_4440)
-- Data.Nat.Properties.⊓-⊔-latticeProperties.⊓-isSemilattice
d_'8851''45'isSemilattice_4694 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
d_'8851''45'isSemilattice_4694
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'isSemilattice_602
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-latticeProperties.⊓-semilattice
d_'8851''45'semilattice_4696 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8851''45'semilattice_4696
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'semilattice_604
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-⊔-latticeProperties.⊔-⊓-distributiveLattice
d_'8852''45''8851''45'distributiveLattice_4698 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584
d_'8852''45''8851''45'distributiveLattice_4698
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'distributiveLattice_806
      (coe d_'8804''45'totalPreorder_2822)
      (coe d_'8851''45'operator_4438) (coe d_'8852''45'operator_4440)
-- Data.Nat.Properties.⊓-⊔-latticeProperties.⊔-⊓-isDistributiveLattice
d_'8852''45''8851''45'isDistributiveLattice_4700 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036
d_'8852''45''8851''45'isDistributiveLattice_4700
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'isDistributiveLattice_800
      (coe d_'8804''45'totalPreorder_2822)
      (coe d_'8851''45'operator_4438) (coe d_'8852''45'operator_4440)
-- Data.Nat.Properties.⊓-⊔-latticeProperties.⊔-⊓-isLattice
d_'8852''45''8851''45'isLattice_4702 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962
d_'8852''45''8851''45'isLattice_4702
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'isLattice_794
      (coe d_'8804''45'totalPreorder_2822)
      (coe d_'8851''45'operator_4438) (coe d_'8852''45'operator_4440)
-- Data.Nat.Properties.⊓-⊔-latticeProperties.⊔-⊓-lattice
d_'8852''45''8851''45'lattice_4704 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500
d_'8852''45''8851''45'lattice_4704
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'lattice_802
      (coe d_'8804''45'totalPreorder_2822)
      (coe d_'8851''45'operator_4438) (coe d_'8852''45'operator_4440)
-- Data.Nat.Properties.⊔-identityˡ
d_'8852''45'identity'737'_4706 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852''45'identity'737'_4706 = erased
-- Data.Nat.Properties.⊔-identityʳ
d_'8852''45'identity'691'_4708 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852''45'identity'691'_4708 = erased
-- Data.Nat.Properties.⊔-identity
d_'8852''45'identity_4712 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8852''45'identity_4712
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.⊔-0-isMonoid
d_'8852''45'0'45'isMonoid_4714 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'8852''45'0'45'isMonoid_4714
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMonoid'46'constructor_15845
      (let v0 = d_'8804''45'totalPreorder_2822 in
       coe
         (let v1 = d_'8852''45'operator_4440 in
          coe
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSemigroup_3032
               (coe
                  MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                  (coe v0))
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                  (coe v1)))))
      (coe d_'8852''45'identity_4712)
-- Data.Nat.Properties.⊔-0-isCommutativeMonoid
d_'8852''45'0'45'isCommutativeMonoid_4716 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_'8852''45'0'45'isCommutativeMonoid_4716
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeMonoid'46'constructor_17665
      (coe d_'8852''45'0'45'isMonoid_4714)
      (let v0 = d_'8804''45'totalPreorder_2822 in
       coe
         (let v1 = d_'8852''45'operator_4440 in
          coe
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'comm_2856
               (coe
                  MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                  (coe v0))
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                  (coe v1)))))
-- Data.Nat.Properties.⊔-0-monoid
d_'8852''45'0'45'monoid_4718 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
d_'8852''45'0'45'monoid_4718
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Monoid'46'constructor_15973
      MAlonzo.Code.Data.Nat.Base.d__'8852'__204 (0 :: Integer)
      d_'8852''45'0'45'isMonoid_4714
-- Data.Nat.Properties.⊔-0-commutativeMonoid
d_'8852''45'0'45'commutativeMonoid_4720 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_962
d_'8852''45'0'45'commutativeMonoid_4720
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeMonoid'46'constructor_17727
      MAlonzo.Code.Data.Nat.Base.d__'8852'__204 (0 :: Integer)
      d_'8852''45'0'45'isCommutativeMonoid_4716
-- Data.Nat.Properties.mono-≤-distrib-⊔
d_mono'45''8804''45'distrib'45''8852'_4728 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono'45''8804''45'distrib'45''8852'_4728 = erased
-- Data.Nat.Properties.mono-≤-distrib-⊓
d_mono'45''8804''45'distrib'45''8851'_4738 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mono'45''8804''45'distrib'45''8851'_4738 = erased
-- Data.Nat.Properties.antimono-≤-distrib-⊓
d_antimono'45''8804''45'distrib'45''8851'_4748 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antimono'45''8804''45'distrib'45''8851'_4748 = erased
-- Data.Nat.Properties.antimono-≤-distrib-⊔
d_antimono'45''8804''45'distrib'45''8852'_4758 ::
  (Integer -> Integer) ->
  (Integer ->
   Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22) ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_antimono'45''8804''45'distrib'45''8852'_4758 = erased
-- Data.Nat.Properties.m<n⇒m<n⊔o
d_m'60'n'8658'm'60'n'8852'o_4764 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'8658'm'60'n'8852'o_4764 v0 v1
  = let v2 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v3 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'x'8851'z'8804'y_3160
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v2))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v3))
            (coe v1) (coe addInt (coe (1 :: Integer)) (coe v0))))
-- Data.Nat.Properties.m<n⇒m<o⊔n
d_m'60'n'8658'm'60'o'8852'n_4768 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'8658'm'60'o'8852'n_4768 v0 v1
  = let v2 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v3 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'z'8851'x'8804'y_3172
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v2))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v3))
            (coe v1) (coe addInt (coe (1 :: Integer)) (coe v0))))
-- Data.Nat.Properties.m⊔n<o⇒m<o
d_m'8852'n'60'o'8658'm'60'o_4776 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8852'n'60'o'8658'm'60'o_4776 v0 v1 ~v2 v3
  = du_m'8852'n'60'o'8658'm'60'o_4776 v0 v1 v3
du_m'8852'n'60'o'8658'm'60'o_4776 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8852'n'60'o'8658'm'60'o_4776 v0 v1 v2
  = coe
      du_'8804''45''60''45'trans_2986
      (let v3 = d_'8804''45'totalPreorder_2822 in
       coe
         (let v4 = d_'8852''45'operator_4440 in
          coe
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2808
               (coe
                  MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                  (coe v3))
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                  (coe v4))
               (coe v0) (coe v1))))
      (coe v2)
-- Data.Nat.Properties.m⊔n<o⇒n<o
d_m'8852'n'60'o'8658'n'60'o_4790 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8852'n'60'o'8658'n'60'o_4790 v0 v1 ~v2 v3
  = du_m'8852'n'60'o'8658'n'60'o_4790 v0 v1 v3
du_m'8852'n'60'o'8658'n'60'o_4790 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8852'n'60'o'8658'n'60'o_4790 v0 v1 v2
  = coe
      du_'8804''45''60''45'trans_2986
      (let v3 = d_'8804''45'totalPreorder_2822 in
       coe
         (let v4 = d_'8852''45'operator_4440 in
          coe
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2834
               (coe
                  MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
                  (coe v3))
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
                  (coe v4))
               (coe v0) (coe v1))))
      (coe v2)
-- Data.Nat.Properties.⊔-mono-<
d_'8852''45'mono'45''60'_4798 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8852''45'mono'45''60'_4798 v0 v1 v2 v3
  = let v4 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v5 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'45''8804'_3206
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v4))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v5))
            (coe v1) (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v3)
            (coe addInt (coe (1 :: Integer)) (coe v2))))
-- Data.Nat.Properties.⊔-pres-<m
d_'8852''45'pres'45''60'm_4800 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8852''45'pres'45''60'm_4800 v0 v1 v2 v3 v4
  = coe d_'8852''45'mono'45''60'_4798 v0 v1 v2 v1 v3 v4
-- Data.Nat.Properties.+-distribˡ-⊔
d_'43''45'distrib'737''45''8852'_4810 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'distrib'737''45''8852'_4810 = erased
-- Data.Nat.Properties.+-distribʳ-⊔
d_'43''45'distrib'691''45''8852'_4822 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'distrib'691''45''8852'_4822 = erased
-- Data.Nat.Properties.+-distrib-⊔
d_'43''45'distrib'45''8852'_4824 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'distrib'45''8852'_4824
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.m⊔n≤m+n
d_m'8852'n'8804'm'43'n_4830 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8852'n'8804'm'43'n_4830 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52
              (coe
                 (\ v2 ->
                    coe
                      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8852'y'8776'x_156
                         d_'8852''45'operator_4440 v0 v1 v2)))
              (coe
                 (\ v2 ->
                    coe
                      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8852'y'8776'y_150
                         d_'8852''45'operator_4440 v0 v1 v2)))
              (coe d_'8804''45'total_2790 (coe v1) (coe v0)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
           -> coe du_m'8804'm'43'n_3482 (coe v0)
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
           -> coe du_m'8804'n'43'm_3494 (coe v1)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.*-distribˡ-⊔
d_'42''45'distrib'737''45''8852'_4860 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''8852'_4860 = erased
-- Data.Nat.Properties.*-distribʳ-⊔
d_'42''45'distrib'691''45''8852'_4882 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''8852'_4882 = erased
-- Data.Nat.Properties.*-distrib-⊔
d_'42''45'distrib'45''8852'_4884 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'distrib'45''8852'_4884
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.⊓-zeroˡ
d_'8851''45'zero'737'_4886 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'zero'737'_4886 = erased
-- Data.Nat.Properties.⊓-zeroʳ
d_'8851''45'zero'691'_4888 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'zero'691'_4888 = erased
-- Data.Nat.Properties.⊓-zero
d_'8851''45'zero_4892 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'zero_4892
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.⊔-⊓-isSemiringWithoutOne
d_'8852''45''8851''45'isSemiringWithoutOne_4894 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1298
d_'8852''45''8851''45'isSemiringWithoutOne_4894
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemiringWithoutOne'46'constructor_37557
      (coe d_'8852''45'0'45'isCommutativeMonoid_4716) erased
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'assoc_2944
         (coe d_'8804''45'totalPreorder_2822)
         (coe d_'8851''45'operator_4438))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8851''45'distrib'45''8852'_3138
         (coe d_'8804''45'totalPreorder_2822)
         (coe d_'8851''45'operator_4438) (coe d_'8852''45'operator_4440))
      (coe d_'8851''45'zero_4892)
-- Data.Nat.Properties.⊔-⊓-isCommutativeSemiringWithoutOne
d_'8852''45''8851''45'isCommutativeSemiringWithoutOne_4896 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1382
d_'8852''45''8851''45'isCommutativeSemiringWithoutOne_4896
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeSemiringWithoutOne'46'constructor_41365
      (coe d_'8852''45''8851''45'isSemiringWithoutOne_4894)
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'comm_2856
         (coe d_'8804''45'totalPreorder_2822)
         (coe d_'8851''45'operator_4438))
-- Data.Nat.Properties.⊔-⊓-commutativeSemiringWithoutOne
d_'8852''45''8851''45'commutativeSemiringWithoutOne_4898 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiringWithoutOne_2002
d_'8852''45''8851''45'commutativeSemiringWithoutOne_4898
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeSemiringWithoutOne'46'constructor_36425
      MAlonzo.Code.Data.Nat.Base.d__'8852'__204
      MAlonzo.Code.Data.Nat.Base.d__'8851'__232 (0 :: Integer)
      d_'8852''45''8851''45'isCommutativeSemiringWithoutOne_4896
-- Data.Nat.Properties.m<n⇒m⊓o<n
d_m'60'n'8658'm'8851'o'60'n_4902 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'8658'm'8851'o'60'n_4902 v0 ~v1 v2 v3
  = du_m'60'n'8658'm'8851'o'60'n_4902 v0 v2 v3
du_m'60'n'8658'm'8851'o'60'n_4902 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'n'8658'm'8851'o'60'n_4902 v0 v1 v2
  = coe
      du_'8804''45''60''45'trans_2986
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2808
         (coe d_'8804''45'totalPreorder_2822)
         (coe d_'8851''45'operator_4438) (coe v0) (coe v1))
      (coe v2)
-- Data.Nat.Properties.m<n⇒o⊓m<n
d_m'60'n'8658'o'8851'm'60'n_4910 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'8658'o'8851'm'60'n_4910 v0 ~v1 v2 v3
  = du_m'60'n'8658'o'8851'm'60'n_4910 v0 v2 v3
du_m'60'n'8658'o'8851'm'60'n_4910 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'n'8658'o'8851'm'60'n_4910 v0 v1 v2
  = coe
      du_'8804''45''60''45'trans_2986
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2834
         (coe d_'8804''45'totalPreorder_2822)
         (coe d_'8851''45'operator_4438) (coe v1) (coe v0))
      (coe v2)
-- Data.Nat.Properties.m<n⊓o⇒m<n
d_m'60'n'8851'o'8658'm'60'n_4920 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'8851'o'8658'm'60'n_4920 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'y_3184
      (coe d_'8804''45'totalPreorder_2822)
      (coe d_'8851''45'operator_4438)
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- Data.Nat.Properties.m<n⊓o⇒m<o
d_m'60'n'8851'o'8658'm'60'o_4926 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'8851'o'8658'm'60'o_4926 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'z_3198
      (coe d_'8804''45'totalPreorder_2822)
      (coe d_'8851''45'operator_4438)
      (coe addInt (coe (1 :: Integer)) (coe v0))
-- Data.Nat.Properties.⊓-mono-<
d_'8851''45'mono'45''60'_4928 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8851''45'mono'45''60'_4928 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'45''8804'_3206
      (coe d_'8804''45'totalPreorder_2822)
      (coe d_'8851''45'operator_4438)
      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1)
      (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v3)
-- Data.Nat.Properties.⊓-pres-m<
d_'8851''45'pres'45'm'60'_4930 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8851''45'pres'45'm'60'_4930 v0 v1 v2 v3 v4
  = coe d_'8851''45'mono'45''60'_4928 v0 v1 v0 v2 v3 v4
-- Data.Nat.Properties.+-distribˡ-⊓
d_'43''45'distrib'737''45''8851'_4940 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'distrib'737''45''8851'_4940 = erased
-- Data.Nat.Properties.+-distribʳ-⊓
d_'43''45'distrib'691''45''8851'_4952 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'distrib'691''45''8851'_4952 = erased
-- Data.Nat.Properties.+-distrib-⊓
d_'43''45'distrib'45''8851'_4954 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'distrib'45''8851'_4954
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.m⊓n≤m+n
d_m'8851'n'8804'm'43'n_4960 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8851'n'8804'm'43'n_4960 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52
              (coe
                 (\ v2 ->
                    coe
                      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_120
                         d_'8851''45'operator_4438 v0 v1 v2)))
              (coe
                 (\ v2 ->
                    coe
                      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_126
                         d_'8851''45'operator_4438 v0 v1 v2)))
              (coe d_'8804''45'total_2790 (coe v0) (coe v1)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
           -> coe du_m'8804'm'43'n_3482 (coe v0)
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
           -> coe du_m'8804'n'43'm_3494 (coe v1)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.*-distribˡ-⊓
d_'42''45'distrib'737''45''8851'_4990 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''8851'_4990 = erased
-- Data.Nat.Properties.*-distribʳ-⊓
d_'42''45'distrib'691''45''8851'_5012 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''8851'_5012 = erased
-- Data.Nat.Properties.*-distrib-⊓
d_'42''45'distrib'45''8851'_5014 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'distrib'45''8851'_5014
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.0∸n≡0
d_0'8760'n'8801'0_5016 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_0'8760'n'8801'0_5016 = erased
-- Data.Nat.Properties.n∸n≡0
d_n'8760'n'8801'0_5020 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'8760'n'8801'0_5020 = erased
-- Data.Nat.Properties.pred[m∸n]≡m∸[1+n]
d_pred'91'm'8760'n'93''8801'm'8760''91'1'43'n'93'_5028 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pred'91'm'8760'n'93''8801'm'8760''91'1'43'n'93'_5028 = erased
-- Data.Nat.Properties.m∸n≤m
d_m'8760'n'8804'm_5042 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8760'n'8804'm_5042 v0 v1
  = case coe v1 of
      0 -> coe
             d_'8804''45'refl_2776
             (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 (0 :: Integer))
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                0 -> coe
                       d_'8804''45'refl_2776
                       (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 (0 :: Integer) v1)
                _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
                     coe
                       (coe
                          du_'8804''45'trans_2784
                          (coe d_m'8760'n'8804'm_5042 (coe v3) (coe v2))
                          (coe d_n'8804'1'43'n_2844 (coe v3))))
-- Data.Nat.Properties.m≮m∸n
d_m'8814'm'8760'n_5056 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_m'8814'm'8760'n_5056 = erased
-- Data.Nat.Properties.1+m≢m∸n
d_1'43'm'8802'm'8760'n_5068 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_1'43'm'8802'm'8760'n_5068 = erased
-- Data.Nat.Properties.∸-mono
d_'8760''45'mono_5076 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8760''45'mono_5076 v0 v1 v2 v3 v4 v5
  = let v6
          = seq
              (coe v5)
              (coe
                 du_'8804''45'trans_2784
                 (coe d_m'8760'n'8804'm_5042 (coe v0) (coe v2)) (coe v4)) in
    coe
      (case coe v4 of
         MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
           -> case coe v5 of
                MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                  -> coe
                       du_'8804''45'trans_2784
                       (coe d_m'8760'n'8804'm_5042 (coe v0) (coe v2))
                       (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v10
                  -> case coe v2 of
                       _ | coe geqInt (coe v2) (coe (1 :: Integer)) ->
                           case coe v3 of
                             _ | coe geqInt (coe v3) (coe (1 :: Integer)) ->
                                 coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                             _ -> coe v6
                       _ -> coe v6
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9
           -> let v10
                    = seq
                        (coe v5)
                        (coe
                           du_'8804''45'trans_2784
                           (coe d_m'8760'n'8804'm_5042 (coe v0) (coe v2))
                           (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9)) in
              coe
                (case coe v0 of
                   _ | coe geqInt (coe v0) (coe (1 :: Integer)) ->
                       let v11 = subInt (coe v0) (coe (1 :: Integer)) in
                       coe
                         (let v12
                                = seq
                                    (coe v5)
                                    (coe
                                       du_'8804''45'trans_2784
                                       (coe d_m'8760'n'8804'm_5042 (coe v0) (coe v2))
                                       (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9)) in
                          coe
                            (case coe v1 of
                               _ | coe geqInt (coe v1) (coe (1 :: Integer)) ->
                                   let v13 = subInt (coe v1) (coe (1 :: Integer)) in
                                   coe
                                     (case coe v5 of
                                        MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                                          -> coe
                                               du_'8804''45'trans_2784
                                               (coe d_m'8760'n'8804'm_5042 (coe v0) (coe v2))
                                               (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9)
                                        MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v16
                                          -> case coe v2 of
                                               _ | coe geqInt (coe v2) (coe (1 :: Integer)) ->
                                                   let v17 = subInt (coe v2) (coe (1 :: Integer)) in
                                                   coe
                                                     (case coe v3 of
                                                        _ | coe
                                                              geqInt (coe v3)
                                                              (coe (1 :: Integer)) ->
                                                            let v18
                                                                  = subInt
                                                                      (coe v3)
                                                                      (coe (1 :: Integer)) in
                                                            coe
                                                              (coe
                                                                 d_'8760''45'mono_5076 (coe v11)
                                                                 (coe v13) (coe v17) (coe v18)
                                                                 (coe v9) (coe v16))
                                                        _ -> coe v12)
                                               _ -> coe v12
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                               _ -> coe v12))
                   _ -> coe v10)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.∸-monoˡ-≤
d_'8760''45'mono'737''45''8804'_5090 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8760''45'mono'737''45''8804'_5090 v0 v1 v2 v3
  = coe
      d_'8760''45'mono_5076 (coe v0) (coe v1) (coe v2) (coe v2) (coe v3)
      (coe d_'8804''45'refl_2776 (coe v2))
-- Data.Nat.Properties.∸-monoʳ-≤
d_'8760''45'mono'691''45''8804'_5098 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8760''45'mono'691''45''8804'_5098 v0 v1 v2 v3
  = coe
      d_'8760''45'mono_5076 (coe v2) (coe v2) (coe v1) (coe v0)
      (coe d_'8804''45'refl_2776 (coe v2)) (coe v3)
-- Data.Nat.Properties.∸-monoˡ-<
d_'8760''45'mono'737''45''60'_5108 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8760''45'mono'737''45''60'_5108 ~v0 v1 ~v2 v3 v4
  = du_'8760''45'mono'737''45''60'_5108 v1 v3 v4
du_'8760''45'mono'737''45''60'_5108 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8760''45'mono'737''45''60'_5108 v0 v1 v2
  = case coe v0 of
      0 -> coe v1
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
                  -> case coe v2 of
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9
                         -> coe
                              du_'8760''45'mono'737''45''60'_5108 (coe v3) (coe v6) (coe v9)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.∸-monoʳ-<
d_'8760''45'mono'691''45''60'_5134 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8760''45'mono'691''45''60'_5134 v0 v1 v2 v3 v4
  = let v5 = subInt (coe v1) (coe (1 :: Integer)) in
    coe
      (case coe v2 of
         0 -> coe
                seq (coe v3)
                (coe
                   seq (coe v4)
                   (coe
                      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                      (d_m'8760'n'8804'm_5042
                         (coe subInt (coe v0) (coe (1 :: Integer))) (coe v5))))
         _ -> let v6 = subInt (coe v2) (coe (1 :: Integer)) in
              coe
                (case coe v3 of
                   MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v9
                     -> case coe v4 of
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v12
                            -> let v13 = subInt (coe v0) (coe (1 :: Integer)) in
                               coe
                                 (coe
                                    d_'8760''45'mono'691''45''60'_5134 (coe v13) (coe v5) (coe v6)
                                    (coe v9) (coe v12))
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError))
-- Data.Nat.Properties.∸-cancelʳ-≤
d_'8760''45'cancel'691''45''8804'_5156 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8760''45'cancel'691''45''8804'_5156 ~v0 v1 ~v2 v3 ~v4
  = du_'8760''45'cancel'691''45''8804'_5156 v1 v3
du_'8760''45'cancel'691''45''8804'_5156 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8760''45'cancel'691''45''8804'_5156 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
        -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v4
        -> case coe v0 of
             0 -> coe
                    MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                    erased
             _ -> let v5 = subInt (coe v0) (coe (1 :: Integer)) in
                  coe
                    (coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (coe du_'8760''45'cancel'691''45''8804'_5156 (coe v5) (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.∸-cancelʳ-<
d_'8760''45'cancel'691''45''60'_5176 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8760''45'cancel'691''45''60'_5176 v0 v1 ~v2 ~v3
  = du_'8760''45'cancel'691''45''60'_5176 v0 v1
du_'8760''45'cancel'691''45''60'_5176 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8760''45'cancel'691''45''60'_5176 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
             erased
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe du_0'60'1'43'n_3074
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (coe du_'8760''45'cancel'691''45''60'_5176 (coe v2) (coe v3))))
-- Data.Nat.Properties.∸-cancelˡ-≡
d_'8760''45'cancel'737''45''8801'_5196 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8760''45'cancel'737''45''8801'_5196 = erased
-- Data.Nat.Properties.∸-cancelʳ-≡
d_'8760''45'cancel'691''45''8801'_5212 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8760''45'cancel'691''45''8801'_5212 = erased
-- Data.Nat.Properties.m∸n≡0⇒m≤n
d_m'8760'n'8801'0'8658'm'8804'n_5222 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8760'n'8801'0'8658'm'8804'n_5222 v0 ~v1 ~v2
  = du_m'8760'n'8801'0'8658'm'8804'n_5222 v0
du_m'8760'n'8801'0'8658'm'8804'n_5222 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8760'n'8801'0'8658'm'8804'n_5222 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (coe du_m'8760'n'8801'0'8658'm'8804'n_5222 (coe v1)))
-- Data.Nat.Properties.m≤n⇒m∸n≡0
d_m'8804'n'8658'm'8760'n'8801'0_5230 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8804'n'8658'm'8760'n'8801'0_5230 = erased
-- Data.Nat.Properties.m<n⇒0<n∸m
d_m'60'n'8658'0'60'n'8760'm_5236 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'8658'0'60'n'8760'm_5236 v0 ~v1 v2
  = du_m'60'n'8658'0'60'n'8760'm_5236 v0 v2
du_m'60'n'8658'0'60'n'8760'm_5236 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'n'8658'0'60'n'8760'm_5236 v0 v1
  = case coe v0 of
      0 -> coe du_0'60'1'43'n_3074
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5
                  -> coe du_m'60'n'8658'0'60'n'8760'm_5236 (coe v2) (coe v5)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.m∸n≢0⇒n<m
d_m'8760'n'8802'0'8658'n'60'm_5246 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8760'n'8802'0'8658'n'60'm_5246 v0 v1 ~v2
  = du_m'8760'n'8802'0'8658'n'60'm_5246 v0 v1
du_m'8760'n'8802'0'8658'n'60'm_5246 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8760'n'8802'0'8658'n'60'm_5246 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
              (\ v2 ->
                 coe
                   du_'8804''7495''8658''8804'_2746
                   (coe addInt (coe (1 :: Integer)) (coe v1)))
              (coe du_'8804''8658''8804''7495'_2758)
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_66
                 (coe
                    MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                    (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v0))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v5 -> coe v5
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                          erased)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.m>n⇒m∸n≢0
d_m'62'n'8658'm'8760'n'8802'0_5274 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_m'62'n'8658'm'8760'n'8802'0_5274 = erased
-- Data.Nat.Properties.m≤n⇒n∸m≤n
d_m'8804'n'8658'n'8760'm'8804'n_5280 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'n'8658'n'8760'm'8804'n_5280 ~v0 v1 v2
  = du_m'8804'n'8658'n'8760'm'8804'n_5280 v1 v2
du_m'8804'n'8658'n'8760'm'8804'n_5280 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'n'8658'n'8760'm'8804'n_5280 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
        -> coe
             d_'8804''45'refl_2776
             (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 (0 :: Integer))
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v4
        -> let v5 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe du_m'8804'n'8658'n'8760'm'8804'n_5280 (coe v5) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.+-∸-comm
d_'43''45''8760''45'comm_5290 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45''8760''45'comm_5290 = erased
-- Data.Nat.Properties.∸-+-assoc
d_'8760''45''43''45'assoc_5308 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8760''45''43''45'assoc_5308 = erased
-- Data.Nat.Properties.+-∸-assoc
d_'43''45''8760''45'assoc_5332 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45''8760''45'assoc_5332 = erased
-- Data.Nat.Properties.m≤n+o⇒m∸n≤o
d_m'8804'n'43'o'8658'm'8760'n'8804'o_5354 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'n'43'o'8658'm'8760'n'8804'o_5354 v0 v1 ~v2 v3
  = du_m'8804'n'43'o'8658'm'8760'n'8804'o_5354 v0 v1 v3
du_m'8804'n'43'o'8658'm'8760'n'8804'o_5354 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'n'43'o'8658'm'8760'n'8804'o_5354 v0 v1 v2
  = case coe v1 of
      0 -> coe v2
      _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                _ -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
                     coe
                       (coe
                          du_m'8804'n'43'o'8658'm'8760'n'8804'o_5354 (coe v4) (coe v3)
                          (coe
                             MAlonzo.Code.Data.Nat.Base.du_s'8804's'8315''185'_62 (coe v2))))
-- Data.Nat.Properties.m<n+o⇒m∸n<o
d_m'60'n'43'o'8658'm'8760'n'60'o_5374 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'60'n'43'o'8658'm'8760'n'60'o_5374 v0 v1 ~v2 ~v3 v4
  = du_m'60'n'43'o'8658'm'8760'n'60'o_5374 v0 v1 v4
du_m'60'n'43'o'8658'm'8760'n'60'o_5374 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'60'n'43'o'8658'm'8760'n'60'o_5374 v0 v1 v2
  = case coe v1 of
      0 -> coe v2
      _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v0 of
                0 -> coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
                _ -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
                     coe
                       (coe
                          du_m'60'n'43'o'8658'm'8760'n'60'o_5374 (coe v4) (coe v3)
                          (coe MAlonzo.Code.Data.Nat.Base.du_s'60's'8315''185'_70 (coe v2))))
-- Data.Nat.Properties.m+n≤o⇒m≤o∸n
d_m'43'n'8804'o'8658'm'8804'o'8760'n_5398 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'43'n'8804'o'8658'm'8804'o'8760'n_5398 v0 ~v1 ~v2 v3
  = du_m'43'n'8804'o'8658'm'8804'o'8760'n_5398 v0 v3
du_m'43'n'8804'o'8658'm'8804'o'8760'n_5398 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'43'n'8804'o'8658'm'8804'o'8760'n_5398 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v5
                  -> coe
                       MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                       (coe du_m'43'n'8804'o'8658'm'8804'o'8760'n_5398 (coe v2) (coe v5))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.m≤o∸n⇒m+n≤o
d_m'8804'o'8760'n'8658'm'43'n'8804'o_5418 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'o'8760'n'8658'm'43'n'8804'o_5418 ~v0 ~v1 ~v2 v3 v4
  = du_m'8804'o'8760'n'8658'm'43'n'8804'o_5418 v3 v4
du_m'8804'o'8760'n'8658'm'43'n'8804'o_5418 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_m'8804'o'8760'n'8658'm'43'n'8804'o_5418 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26 -> coe v1
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v4
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe du_m'8804'o'8760'n'8658'm'43'n'8804'o_5418 (coe v4) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.m≤n+m∸n
d_m'8804'n'43'm'8760'n_5444 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'n'43'm'8760'n_5444 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe d_'8804''45'refl_2776 (coe v0)
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (d_m'8804'n'43'm'8760'n_5444 (coe v2) (coe v3))))
-- Data.Nat.Properties.m+n∸n≡m
d_m'43'n'8760'n'8801'm_5458 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'43'n'8760'n'8801'm_5458 = erased
-- Data.Nat.Properties.m+n∸m≡n
d_m'43'n'8760'm'8801'n_5470 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'43'n'8760'm'8801'n_5470 = erased
-- Data.Nat.Properties.m+[n∸m]≡n
d_m'43''91'n'8760'm'93''8801'n_5478 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'43''91'n'8760'm'93''8801'n_5478 = erased
-- Data.Nat.Properties.m∸n+n≡m
d_m'8760'n'43'n'8801'm_5492 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8760'n'43'n'8801'm_5492 = erased
-- Data.Nat.Properties.m∸[m∸n]≡n
d_m'8760''91'm'8760'n'93''8801'n_5504 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8760''91'm'8760'n'93''8801'n_5504 = erased
-- Data.Nat.Properties.[m+n]∸[m+o]≡n∸o
d_'91'm'43'n'93''8760''91'm'43'o'93''8801'n'8760'o_5520 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'91'm'43'n'93''8760''91'm'43'o'93''8801'n'8760'o_5520 = erased
-- Data.Nat.Properties.*-distribʳ-∸
d_'42''45'distrib'691''45''8760'_5532 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''8760'_5532 = erased
-- Data.Nat.Properties.*-distribˡ-∸
d_'42''45'distrib'737''45''8760'_5552 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''8760'_5552 = erased
-- Data.Nat.Properties.*-distrib-∸
d_'42''45'distrib'45''8760'_5554 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'distrib'45''8760'_5554
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.even≢odd
d_even'8802'odd_5560 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_even'8802'odd_5560 = erased
-- Data.Nat.Properties.m⊓n+n∸m≡n
d_m'8851'n'43'n'8760'm'8801'n_5576 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8851'n'43'n'8760'm'8801'n_5576 = erased
-- Data.Nat.Properties.[m∸n]⊓[n∸m]≡0
d_'91'm'8760'n'93''8851''91'n'8760'm'93''8801'0_5590 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'91'm'8760'n'93''8851''91'n'8760'm'93''8801'0_5590 = erased
-- Data.Nat.Properties.∸-distribˡ-⊓-⊔
d_'8760''45'distrib'737''45''8851''45''8852'_5606 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8760''45'distrib'737''45''8851''45''8852'_5606 = erased
-- Data.Nat.Properties.∸-distribʳ-⊓
d_'8760''45'distrib'691''45''8851'_5614 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8760''45'distrib'691''45''8851'_5614 = erased
-- Data.Nat.Properties.∸-distribˡ-⊔-⊓
d_'8760''45'distrib'737''45''8852''45''8851'_5628 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8760''45'distrib'737''45''8852''45''8851'_5628 = erased
-- Data.Nat.Properties.∸-distribʳ-⊔
d_'8760''45'distrib'691''45''8852'_5636 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8760''45'distrib'691''45''8852'_5636 = erased
-- Data.Nat.Properties.pred[n]≤n
d_pred'91'n'93''8804'n_5644 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pred'91'n'93''8804'n_5644 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe d_n'8804'1'43'n_2844 (coe v1))
-- Data.Nat.Properties.≤pred⇒≤
d_'8804'pred'8658''8804'_5648 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804'pred'8658''8804'_5648 ~v0 v1 v2
  = du_'8804'pred'8658''8804'_5648 v1 v2
du_'8804'pred'8658''8804'_5648 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804'pred'8658''8804'_5648 v0 v1 = coe seq (coe v0) (coe v1)
-- Data.Nat.Properties.≤⇒pred≤
d_'8804''8658'pred'8804'_5656 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''8658'pred'8804'_5656 v0 ~v1 v2
  = du_'8804''8658'pred'8804'_5656 v0 v2
du_'8804''8658'pred'8804'_5656 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''8658'pred'8804'_5656 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                du_'8804''45'trans_2784 (coe d_n'8804'1'43'n_2844 (coe v2))
                (coe v1))
-- Data.Nat.Properties.<⇒≤pred
d_'60''8658''8804'pred_5664 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''8658''8804'pred_5664 ~v0 ~v1 v2
  = du_'60''8658''8804'pred_5664 v2
du_'60''8658''8804'pred_5664 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''8658''8804'pred_5664 v0
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.suc-pred
d_suc'45'pred_5672 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'45'pred_5672 = erased
-- Data.Nat.Properties.pred-mono-≤
d_pred'45'mono'45''8804'_5676 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pred'45'mono'45''8804'_5676 v0 ~v1 v2
  = du_pred'45'mono'45''8804'_5676 v0 v2
du_pred'45'mono'45''8804'_5676 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_pred'45'mono'45''8804'_5676 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> coe
             MAlonzo.Code.Data.Nat.Base.du_s'8804's'8315''185'_62 (coe v1)
-- Data.Nat.Properties.pred-mono-<
d_pred'45'mono'45''60'_5680 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pred'45'mono'45''60'_5680 v0 v1 ~v2
  = du_pred'45'mono'45''60'_5680 v0 v1
du_pred'45'mono'45''60'_5680 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_pred'45'mono'45''60'_5680 v0 v1
  = case coe v0 of
      0 -> coe (\ v2 -> MAlonzo.RTE.mazUnreachableError)
      _ -> case coe v1 of
             0 -> coe (\ v2 -> MAlonzo.RTE.mazUnreachableError)
             _ -> coe MAlonzo.Code.Data.Nat.Base.du_s'60's'8315''185'_70
-- Data.Nat.Properties.pred-cancel-≤
d_pred'45'cancel'45''8804'_5682 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_pred'45'cancel'45''8804'_5682 v0 v1 v2
  = case coe v0 of
      0 -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      _ -> case coe v1 of
             0 -> coe
                    seq (coe v2)
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
             _ -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v2)
-- Data.Nat.Properties.pred-cancel-<
d_pred'45'cancel'45''60'_5686 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pred'45'cancel'45''60'_5686 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             0 -> coe (\ v2 -> MAlonzo.RTE.mazUnreachableError)
             _ -> coe
                    (\ v2 ->
                       coe
                         MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
      _ -> case coe v1 of
             0 -> coe (\ v2 -> MAlonzo.RTE.mazUnreachableError)
             _ -> coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
-- Data.Nat.Properties.pred-injective
d_pred'45'injective_5688 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pred'45'injective_5688 = erased
-- Data.Nat.Properties.pred-cancel-≡
d_pred'45'cancel'45''8801'_5694 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_pred'45'cancel'45''8801'_5694 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             0 -> coe
                    (\ v2 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased)
             _ -> coe
                    (\ v2 ->
                       coe
                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                         (coe
                            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                            (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)))
      _ -> case coe v1 of
             0 -> coe
                    (\ v2 ->
                       coe
                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                         (coe
                            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                            (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)))
             _ -> coe
                    (\ v2 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased)
-- Data.Nat.Properties.m≡n⇒∣m-n∣≡0
d_m'8801'n'8658''8739'm'45'n'8739''8801'0_5696 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8801'n'8658''8739'm'45'n'8739''8801'0_5696 = erased
-- Data.Nat.Properties.∣m-n∣≡0⇒m≡n
d_'8739'm'45'n'8739''8801'0'8658'm'8801'n_5700 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'm'45'n'8739''8801'0'8658'm'8801'n_5700 = erased
-- Data.Nat.Properties.m≤n⇒∣n-m∣≡n∸m
d_m'8804'n'8658''8739'n'45'm'8739''8801'n'8760'm_5710 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8804'n'8658''8739'n'45'm'8739''8801'n'8760'm_5710 = erased
-- Data.Nat.Properties.m≤n⇒∣m-n∣≡n∸m
d_m'8804'n'8658''8739'm'45'n'8739''8801'n'8760'm_5716 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8804'n'8658''8739'm'45'n'8739''8801'n'8760'm_5716 = erased
-- Data.Nat.Properties.∣m-n∣≡m∸n⇒n≤m
d_'8739'm'45'n'8739''8801'm'8760'n'8658'n'8804'm_5722 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8739'm'45'n'8739''8801'm'8760'n'8658'n'8804'm_5722 v0 v1 ~v2
  = du_'8739'm'45'n'8739''8801'm'8760'n'8658'n'8804'm_5722 v0 v1
du_'8739'm'45'n'8739''8801'm'8760'n'8658'n'8804'm_5722 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8739'm'45'n'8739''8801'm'8760'n'8658'n'8804'm_5722 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (coe
                             du_'8739'm'45'n'8739''8801'm'8760'n'8658'n'8804'm_5722 (coe v2)
                             (coe v3))))
-- Data.Nat.Properties.∣n-n∣≡0
d_'8739'n'45'n'8739''8801'0_5738 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'n'45'n'8739''8801'0_5738 = erased
-- Data.Nat.Properties.∣m-m+n∣≡n
d_'8739'm'45'm'43'n'8739''8801'n_5746 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'm'45'm'43'n'8739''8801'n_5746 = erased
-- Data.Nat.Properties.∣m+n-m+o∣≡∣n-o∣
d_'8739'm'43'n'45'm'43'o'8739''8801''8739'n'45'o'8739'_5760 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'm'43'n'45'm'43'o'8739''8801''8739'n'45'o'8739'_5760
  = erased
-- Data.Nat.Properties.m∸n≤∣m-n∣
d_m'8760'n'8804''8739'm'45'n'8739'_5776 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8760'n'8804''8739'm'45'n'8739'_5776 v0 v1
  = let v2 = d_'8804''45'total_2790 (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
           -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
           -> coe
                d_'8804''45'refl_2776
                (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 v1)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.∣m-n∣≤m⊔n
d_'8739'm'45'n'8739''8804'm'8852'n_5806 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8739'm'45'n'8739''8804'm'8852'n_5806 v0 v1
  = case coe v0 of
      0 -> coe
             d_'8804''45'refl_2776
             (coe
                MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
                (coe (0 :: Integer)) (coe v1))
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe
                       d_'8804''45'refl_2776
                       (coe
                          MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280 (coe v0)
                          (coe (0 :: Integer)))
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (coe d_'8739'm'45'n'8739''8804'm'8852'n_5806 (coe v2) (coe v3)))
-- Data.Nat.Properties.∣-∣-identityˡ
d_'8739''45''8739''45'identity'737'_5816 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''45''8739''45'identity'737'_5816 = erased
-- Data.Nat.Properties.∣-∣-identityʳ
d_'8739''45''8739''45'identity'691'_5820 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''45''8739''45'identity'691'_5820 = erased
-- Data.Nat.Properties.∣-∣-identity
d_'8739''45''8739''45'identity_5824 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8739''45''8739''45'identity_5824
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.∣-∣-comm
d_'8739''45''8739''45'comm_5826 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''45''8739''45'comm_5826 = erased
-- Data.Nat.Properties.∣m-n∣≡[m∸n]∨[n∸m]
d_'8739'm'45'n'8739''8801''91'm'8760'n'93''8744''91'n'8760'm'93'_5840 ::
  Integer -> Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8739'm'45'n'8739''8801''91'm'8760'n'93''8744''91'n'8760'm'93'_5840 v0
                                                                      v1
  = let v2 = d_'8804''45'total_2790 (coe v0) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                (let v4
                       = coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_eqRelation_238 in
                 coe
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                      (coe v4)
                      (coe
                         MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280 (coe v0)
                         (coe v1))
                      (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 v0)
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                         (\ v5 v6 v7 v8 v9 -> v9)
                         (MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
                            (coe v0) (coe v1))
                         (MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
                            (coe v1) (coe v0))
                         (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 v0)
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                            (\ v5 v6 v7 v8 v9 -> v9)
                            (MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
                               (coe v1) (coe v0))
                            (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 v0)
                            (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 v0)
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                               (coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                  (coe d_'8804''45'isPreorder_2810))
                               (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 v0))
                            erased)
                         erased)))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
           -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties.*-distribˡ-∣-∣-aux
d_'42''45'distrib'737''45''8739''45''8739''45'aux_5868 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''8739''45''8739''45'aux_5868 = erased
-- Data.Nat.Properties.*-distribˡ-∣-∣
d_'42''45'distrib'737''45''8739''45''8739'_5880 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'737''45''8739''45''8739'_5880 = erased
-- Data.Nat.Properties.*-distribʳ-∣-∣
d_'42''45'distrib'691''45''8739''45''8739'_5910 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'distrib'691''45''8739''45''8739'_5910 = erased
-- Data.Nat.Properties.*-distrib-∣-∣
d_'42''45'distrib'45''8739''45''8739'_5912 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'distrib'45''8739''45''8739'_5912
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Nat.Properties.m≤n+∣n-m∣
d_m'8804'n'43''8739'n'45'm'8739'_5918 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'n'43''8739'n'45'm'8739'_5918 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe d_'8804''45'refl_2776 (coe v0)
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (coe
                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                          (d_m'8804'n'43''8739'n'45'm'8739'_5918 (coe v2) (coe v3))))
-- Data.Nat.Properties.m≤n+∣m-n∣
d_m'8804'n'43''8739'm'45'n'8739'_5932 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804'n'43''8739'm'45'n'8739'_5932 v0 v1
  = coe d_m'8804'n'43''8739'n'45'm'8739'_5918 (coe v0) (coe v1)
-- Data.Nat.Properties.m≤∣m-n∣+n
d_m'8804''8739'm'45'n'8739''43'n_5946 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_m'8804''8739'm'45'n'8739''43'n_5946 v0 v1
  = coe d_m'8804'n'43''8739'm'45'n'8739'_5932 (coe v0) (coe v1)
-- Data.Nat.Properties.∣-∣-triangle
d_'8739''45''8739''45'triangle_5954 ::
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8739''45''8739''45'triangle_5954 v0 v1 v2
  = case coe v0 of
      0 -> coe d_m'8804'n'43''8739'n'45'm'8739'_5918 (coe v2) (coe v1)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe
                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                          (coe d_'8804''45'isPreorder_2810)
                          (\ v4 v5 v6 -> coe du_'60''8658''8804'_2854 v6))
                       (MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
                          (coe v0) (coe v2))
                       (addInt
                          (coe
                             MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
                             (coe (0 :: Integer)) (coe v2))
                          (coe
                             MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280 (coe v0)
                             (coe (0 :: Integer))))
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                             (coe d_'8804''45'isPreorder_2810)
                             (\ v4 v5 v6 v7 v8 -> coe du_'8804''45''60''45'trans_2986 v7 v8))
                          (MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
                             (coe v0) (coe v2))
                          (MAlonzo.Code.Data.Nat.Base.d__'8852'__204 (coe v0) (coe v2))
                          (addInt
                             (coe
                                MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
                                (coe (0 :: Integer)) (coe v2))
                             (coe
                                MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280 (coe v0)
                                (coe (0 :: Integer))))
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                (coe d_'8804''45'isPreorder_2810)
                                (\ v4 v5 v6 v7 v8 -> coe du_'8804''45''60''45'trans_2986 v7 v8))
                             (MAlonzo.Code.Data.Nat.Base.d__'8852'__204 (coe v0) (coe v2))
                             (addInt (coe v0) (coe v2))
                             (addInt
                                (coe
                                   MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
                                   (coe (0 :: Integer)) (coe v2))
                                (coe
                                   MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280 (coe v0)
                                   (coe (0 :: Integer))))
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                (\ v4 v5 v6 v7 v8 -> v8) (addInt (coe v0) (coe v2))
                                (addInt
                                   (coe
                                      MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280 (coe v0)
                                      (coe (0 :: Integer)))
                                   (coe v2))
                                (addInt
                                   (coe
                                      MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
                                      (coe (0 :: Integer)) (coe v2))
                                   (coe
                                      MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280 (coe v0)
                                      (coe (0 :: Integer))))
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                      (coe d_'8804''45'isPreorder_2810))
                                   (coe
                                      addInt
                                      (coe
                                         MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
                                         (coe v0) (coe (0 :: Integer)))
                                      (coe v2)))
                                erased)
                             (d_m'8852'n'8804'm'43'n_4830 (coe v0) (coe v2)))
                          (d_'8739'm'45'n'8739''8804'm'8852'n_5806 (coe v0) (coe v2)))
                _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (case coe v2 of
                          0 -> coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                                    (coe d_'8804''45'isPreorder_2810)
                                    (\ v5 v6 v7 -> coe du_'60''8658''8804'_2854 v7))
                                 (MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
                                    (coe v0) (coe (0 :: Integer)))
                                 (addInt
                                    (coe
                                       MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280 (coe v0)
                                       (coe v1))
                                    (coe
                                       MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280 (coe v1)
                                       (coe (0 :: Integer))))
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                    (\ v5 v6 v7 v8 v9 -> v9)
                                    (MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
                                       (coe v0) (coe (0 :: Integer)))
                                    v0
                                    (addInt
                                       (coe
                                          MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
                                          (coe v0) (coe v1))
                                       (coe
                                          MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
                                          (coe v1) (coe (0 :: Integer))))
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                          (coe d_'8804''45'isPreorder_2810)
                                          (\ v5 v6 v7 v8 v9 ->
                                             coe du_'8804''45''60''45'trans_2986 v8 v9))
                                       v0
                                       (addInt
                                          (coe
                                             MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
                                             (coe v0) (coe v1))
                                          (coe v1))
                                       (addInt
                                          (coe
                                             MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
                                             (coe v0) (coe v1))
                                          (coe
                                             MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
                                             (coe v1) (coe (0 :: Integer))))
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                          (\ v5 v6 v7 v8 v9 -> v9)
                                          (addInt
                                             (coe
                                                MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
                                                (coe v0) (coe v1))
                                             (coe v1))
                                          (addInt
                                             (coe
                                                MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
                                                (coe v0) (coe v1))
                                             (coe
                                                MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
                                                (coe v1) (coe (0 :: Integer))))
                                          (addInt
                                             (coe
                                                MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
                                                (coe v0) (coe v1))
                                             (coe
                                                MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
                                                (coe v1) (coe (0 :: Integer))))
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                (coe d_'8804''45'isPreorder_2810))
                                             (coe
                                                addInt
                                                (coe
                                                   MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
                                                   (coe v0) (coe v1))
                                                (coe
                                                   MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
                                                   (coe v1) (coe (0 :: Integer)))))
                                          erased)
                                       (d_m'8804''8739'm'45'n'8739''43'n_5946 (coe v0) (coe v1)))
                                    erased)
                          _ -> let v5 = subInt (coe v2) (coe (1 :: Integer)) in
                               coe
                                 (coe
                                    d_'8739''45''8739''45'triangle_5954 (coe v3) (coe v4)
                                    (coe v5))))
-- Data.Nat.Properties.∣-∣≡∣-∣′
d_'8739''45''8739''8801''8739''45''8739''8242'_5986 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''45''8739''8801''8739''45''8739''8242'_5986 = erased
-- Data.Nat.Properties.∣-∣-isProtoMetric
d_'8739''45''8739''45'isProtoMetric_6008 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsProtoMetric_30
d_'8739''45''8739''45'isProtoMetric_6008
  = coe
      MAlonzo.Code.Function.Metric.Structures.C_IsProtoMetric'46'constructor_2109
      (coe d_'8804''45'isPartialOrder_2814)
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      erased
      (coe (\ v0 v1 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
-- Data.Nat.Properties.∣-∣-isPreMetric
d_'8739''45''8739''45'isPreMetric_6010 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsPreMetric_102
d_'8739''45''8739''45'isPreMetric_6010
  = coe
      MAlonzo.Code.Function.Metric.Structures.C_IsPreMetric'46'constructor_6335
      (coe d_'8739''45''8739''45'isProtoMetric_6008) erased
-- Data.Nat.Properties.∣-∣-isQuasiSemiMetric
d_'8739''45''8739''45'isQuasiSemiMetric_6012 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsQuasiSemiMetric_174
d_'8739''45''8739''45'isQuasiSemiMetric_6012
  = coe
      MAlonzo.Code.Function.Metric.Structures.C_IsQuasiSemiMetric'46'constructor_10097
      (coe d_'8739''45''8739''45'isPreMetric_6010) erased
-- Data.Nat.Properties.∣-∣-isSemiMetric
d_'8739''45''8739''45'isSemiMetric_6014 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsSemiMetric_250
d_'8739''45''8739''45'isSemiMetric_6014
  = coe
      MAlonzo.Code.Function.Metric.Structures.C_IsSemiMetric'46'constructor_13989
      (coe d_'8739''45''8739''45'isQuasiSemiMetric_6012) erased
-- Data.Nat.Properties.∣-∣-isMetric
d_'8739''45''8739''45'isMetric_6016 ::
  MAlonzo.Code.Function.Metric.Structures.T_IsGeneralMetric_332
d_'8739''45''8739''45'isMetric_6016
  = coe
      MAlonzo.Code.Function.Metric.Structures.C_IsGeneralMetric'46'constructor_18237
      (coe d_'8739''45''8739''45'isSemiMetric_6014)
      (coe d_'8739''45''8739''45'triangle_5954)
-- Data.Nat.Properties.∣-∣-quasiSemiMetric
d_'8739''45''8739''45'quasiSemiMetric_6018 ::
  MAlonzo.Code.Function.Metric.Nat.Bundles.T_QuasiSemiMetric_186
d_'8739''45''8739''45'quasiSemiMetric_6018
  = coe
      MAlonzo.Code.Function.Metric.Nat.Bundles.C_QuasiSemiMetric'46'constructor_3231
      MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
      d_'8739''45''8739''45'isQuasiSemiMetric_6012
-- Data.Nat.Properties.∣-∣-semiMetric
d_'8739''45''8739''45'semiMetric_6020 ::
  MAlonzo.Code.Function.Metric.Nat.Bundles.T_SemiMetric_284
d_'8739''45''8739''45'semiMetric_6020
  = coe
      MAlonzo.Code.Function.Metric.Nat.Bundles.C_SemiMetric'46'constructor_4955
      MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
      d_'8739''45''8739''45'isSemiMetric_6014
-- Data.Nat.Properties.∣-∣-preMetric
d_'8739''45''8739''45'preMetric_6022 ::
  MAlonzo.Code.Function.Metric.Nat.Bundles.T_PreMetric_96
d_'8739''45''8739''45'preMetric_6022
  = coe
      MAlonzo.Code.Function.Metric.Nat.Bundles.C_PreMetric'46'constructor_1617
      MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
      d_'8739''45''8739''45'isPreMetric_6010
-- Data.Nat.Properties.∣-∣-metric
d_'8739''45''8739''45'metric_6024 ::
  MAlonzo.Code.Function.Metric.Nat.Bundles.T_Metric_388
d_'8739''45''8739''45'metric_6024
  = coe
      MAlonzo.Code.Function.Metric.Nat.Bundles.C_Metric'46'constructor_6749
      MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280
      d_'8739''45''8739''45'isMetric_6016
-- Data.Nat.Properties.⌊n/2⌋-mono
d_'8970'n'47'2'8971''45'mono_6026 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8970'n'47'2'8971''45'mono_6026 ~v0 ~v1 v2
  = du_'8970'n'47'2'8971''45'mono_6026 v2
du_'8970'n'47'2'8971''45'mono_6026 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8970'n'47'2'8971''45'mono_6026 v0
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
        -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v3
        -> case coe v3 of
             MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
               -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
               -> coe
                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                    (coe du_'8970'n'47'2'8971''45'mono_6026 (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.⌈n/2⌉-mono
d_'8968'n'47'2'8969''45'mono_6030 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8968'n'47'2'8969''45'mono_6030 ~v0 ~v1 v2
  = du_'8968'n'47'2'8969''45'mono_6030 v2
du_'8968'n'47'2'8969''45'mono_6030 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8968'n'47'2'8969''45'mono_6030 v0
  = coe
      du_'8970'n'47'2'8971''45'mono_6026
      (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v0)
-- Data.Nat.Properties.⌊n/2⌋≤⌈n/2⌉
d_'8970'n'47'2'8971''8804''8968'n'47'2'8969'_6036 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8970'n'47'2'8971''8804''8968'n'47'2'8969'_6036 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      1 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v1 = subInt (coe v0) (coe (2 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (d_'8970'n'47'2'8971''8804''8968'n'47'2'8969'_6036 (coe v1)))
-- Data.Nat.Properties.⌊n/2⌋+⌈n/2⌉≡n
d_'8970'n'47'2'8971''43''8968'n'47'2'8969''8801'n_6042 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8970'n'47'2'8971''43''8968'n'47'2'8969''8801'n_6042 = erased
-- Data.Nat.Properties.⌊n/2⌋≤n
d_'8970'n'47'2'8971''8804'n_6048 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8970'n'47'2'8971''8804'n_6048 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      1 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v1 = subInt (coe v0) (coe (2 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (d_'8970'n'47'2'8971''8804'n_6048 (coe v1)))
-- Data.Nat.Properties.⌊n/2⌋<n
d_'8970'n'47'2'8971''60'n_6054 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8970'n'47'2'8971''60'n_6054 v0
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (coe
                   MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                   (d_'8970'n'47'2'8971''8804'n_6048 (coe v1))))
-- Data.Nat.Properties.n≡⌊n+n/2⌋
d_n'8801''8970'n'43'n'47'2'8971'_6060 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'8801''8970'n'43'n'47'2'8971'_6060 = erased
-- Data.Nat.Properties.⌈n/2⌉≤n
d_'8968'n'47'2'8969''8804'n_6068 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8968'n'47'2'8969''8804'n_6068 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                (d_'8970'n'47'2'8971''8804'n_6048 (coe v1)))
-- Data.Nat.Properties.⌈n/2⌉<n
d_'8968'n'47'2'8969''60'n_6074 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8968'n'47'2'8969''60'n_6074 v0
  = coe
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
      (d_'8970'n'47'2'8971''60'n_6054 (coe v0))
-- Data.Nat.Properties.n≡⌈n+n/2⌉
d_n'8801''8968'n'43'n'47'2'8969'_6080 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_n'8801''8968'n'43'n'47'2'8969'_6080 = erased
-- Data.Nat.Properties.1≤n!
d_1'8804'n'33'_6088 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_1'8804'n'33'_6088 v0
  = case coe v0 of
      0 -> coe d_'8804''45'refl_2776 (coe (1 :: Integer))
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                du_'42''45'mono'45''8804'_4060 (coe v0)
                (coe MAlonzo.Code.Data.Nat.Base.d__'33'_332 (coe v1))
                (coe du_m'8804'm'43'n_3482 (coe (1 :: Integer)))
                (coe d_1'8804'n'33'_6088 (coe v1)))
-- Data.Nat.Properties._!≢0
d__'33''8802'0_6094 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d__'33''8802'0_6094 v0
  = coe
      MAlonzo.Code.Data.Nat.Base.du_'62''45'nonZero_136
      (coe d_1'8804'n'33'_6088 (coe v0))
-- Data.Nat.Properties._!*_!≢0
d__'33''42'_'33''8802'0_6102 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d__'33''42'_'33''8802'0_6102 ~v0 ~v1
  = du__'33''42'_'33''8802'0_6102
du__'33''42'_'33''8802'0_6102 ::
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du__'33''42'_'33''8802'0_6102 = coe du_m'42'n'8802'0_3840
-- Data.Nat.Properties.≤′-trans
d_'8804''8242''45'trans_6108 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338
d_'8804''8242''45'trans_6108 ~v0 ~v1 ~v2 v3 v4
  = du_'8804''8242''45'trans_6108 v3 v4
du_'8804''8242''45'trans_6108 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338
du_'8804''8242''45'trans_6108 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'refl_342 -> coe v0
      MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'step_348 v3
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'step_348
             (coe du_'8804''8242''45'trans_6108 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.z≤′n
d_z'8804''8242'n_6116 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338
d_z'8804''8242'n_6116 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'refl_342
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'step_348
                (d_z'8804''8242'n_6116 (coe v1)))
-- Data.Nat.Properties.s≤′s
d_s'8804''8242's_6120 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338
d_s'8804''8242's_6120 ~v0 ~v1 v2 = du_s'8804''8242's_6120 v2
du_s'8804''8242's_6120 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338
du_s'8804''8242's_6120 v0 = coe v0
-- Data.Nat.Properties.≤′⇒≤
d_'8804''8242''8658''8804'_6124 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''8242''8658''8804'_6124 v0 ~v1 v2
  = du_'8804''8242''8658''8804'_6124 v0 v2
du_'8804''8242''8658''8804'_6124 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''8242''8658''8804'_6124 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'refl_342
        -> coe d_'8804''45'refl_2776 (coe v0)
      MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'step_348 v3
        -> coe du_'8804''8242''8658''8804'_6124 (coe v0) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.≤⇒≤′
d_'8804''8658''8804''8242'_6128 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338
d_'8804''8658''8804''8242'_6128 ~v0 v1 v2
  = du_'8804''8658''8804''8242'_6128 v1 v2
du_'8804''8658''8804''8242'_6128 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338
du_'8804''8658''8804''8242'_6128 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
        -> coe d_z'8804''8242'n_6116 (coe v0)
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v4
        -> let v5 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe du_'8804''8658''8804''8242'_6128 (coe v5) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.≤′-step-injective
d_'8804''8242''45'step'45'injective_6136 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8242''45'step'45'injective_6136 = erased
-- Data.Nat.Properties.z<′s
d_z'60''8242's_6138 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338
d_z'60''8242's_6138 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'refl_342
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'step_348
                (d_z'60''8242's_6138 (coe v1)))
-- Data.Nat.Properties.s<′s
d_s'60''8242's_6142 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338
d_s'60''8242's_6142 ~v0 ~v1 v2 = du_s'60''8242's_6142 v2
du_s'60''8242's_6142 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338
du_s'60''8242's_6142 v0 = coe v0
-- Data.Nat.Properties.<⇒<′
d_'60''8658''60''8242'_6146 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338
d_'60''8658''60''8242'_6146 ~v0 v1 v2
  = du_'60''8658''60''8242'_6146 v1 v2
du_'60''8658''60''8242'_6146 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338
du_'60''8658''60''8242'_6146 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v4
        -> let v5 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
                  -> coe d_z'60''8242's_6138 (coe v5)
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v8
                  -> coe
                       du_'60''8658''60''8242'_6146
                       (coe subInt (coe v0) (coe (1 :: Integer)))
                       (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v8)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.<′⇒<
d_'60''8242''8658''60'_6150 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''8242''8658''60'_6150 v0 ~v1 v2
  = du_'60''8242''8658''60'_6150 v0 v2
du_'60''8242''8658''60'_6150 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'60''8242''8658''60'_6150 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'refl_342
        -> coe d_n'60'1'43'n_3078 (coe v0)
      MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'step_348 v3
        -> coe
             du_m'60'n'8658'm'60'1'43'n_3062
             (coe du_'60''8242''8658''60'_6150 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.m<1+n⇒m<n∨m≡n′
d_m'60'1'43'n'8658'm'60'n'8744'm'8801'n'8242'_6154 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_m'60'1'43'n'8658'm'60'n'8744'm'8801'n'8242'_6154 v0 v1 v2
  = let v3
          = coe
              du_'60''8658''60''8242'_6146
              (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'refl_342
           -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
         MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'step_348 v5
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                (coe du_'60''8242''8658''60'_6150 (coe v0) (coe v5))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Nat.Properties._≤′?_
d__'8804''8242''63'__6168 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''8242''63'__6168 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
      (coe du_'8804''8658''8804''8242'_6128 (coe v1))
      (coe du_'8804''8242''8658''8804'_6124 (coe v0))
      (coe d__'8804''63'__2802 (coe v0) (coe v1))
-- Data.Nat.Properties._<′?_
d__'60''8242''63'__6174 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''8242''63'__6174 v0 v1
  = coe
      d__'8804''8242''63'__6168
      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1)
-- Data.Nat.Properties._≥′?_
d__'8805''8242''63'__6180 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8805''8242''63'__6180 v0 v1
  = coe d__'8804''8242''63'__6168 (coe v1) (coe v0)
-- Data.Nat.Properties._>′?_
d__'62''8242''63'__6182 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'62''8242''63'__6182 v0 v1
  = coe d__'60''8242''63'__6174 (coe v1) (coe v0)
-- Data.Nat.Properties.m≤′m+n
d_m'8804''8242'm'43'n_6188 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338
d_m'8804''8242'm'43'n_6188 v0 v1
  = coe
      du_'8804''8658''8804''8242'_6128 (coe addInt (coe v0) (coe v1))
      (coe du_m'8804'm'43'n_3482 (coe v0))
-- Data.Nat.Properties.n≤′m+n
d_n'8804''8242'm'43'n_6198 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338
d_n'8804''8242'm'43'n_6198 v0 ~v1 = du_n'8804''8242'm'43'n_6198 v0
du_n'8804''8242'm'43'n_6198 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338
du_n'8804''8242'm'43'n_6198 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'refl_342
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'step_348
                (coe du_n'8804''8242'm'43'n_6198 (coe v1)))
-- Data.Nat.Properties.⌈n/2⌉≤′n
d_'8968'n'47'2'8969''8804''8242'n_6208 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338
d_'8968'n'47'2'8969''8804''8242'n_6208 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'refl_342
      1 -> coe MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'refl_342
      _ -> let v1 = subInt (coe v0) (coe (2 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'step_348
                (d_'8968'n'47'2'8969''8804''8242'n_6208 (coe v1)))
-- Data.Nat.Properties.⌊n/2⌋≤′n
d_'8970'n'47'2'8971''8804''8242'n_6214 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__338
d_'8970'n'47'2'8971''8804''8242'n_6214 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'refl_342
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_'8804''8242''45'step_348
                (d_'8968'n'47'2'8969''8804''8242'n_6208 (coe v1)))
-- Data.Nat.Properties.≤⇒≤″
d_'8804''8658''8804''8243'_6218 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26
d_'8804''8658''8804''8243'_6218 v0 v1 ~v2
  = du_'8804''8658''8804''8243'_6218 v0 v1
du_'8804''8658''8804''8243'_6218 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26
du_'8804''8658''8804''8243'_6218 v0 v1
  = coe
      MAlonzo.Code.Algebra.Definitions.RawMagma.C__'44'__40
      (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 v0) erased
-- Data.Nat.Properties.<⇒<″
d_'60''8658''60''8243'_6222 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26
d_'60''8658''60''8243'_6222 v0 v1 v2
  = coe
      du_'8804''8658''8804''8243'_6218
      (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v1)
-- Data.Nat.Properties.≤″⇒≤
d_'8804''8243''8658''8804'_6224 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''8243''8658''8804'_6224 v0 ~v1 v2
  = du_'8804''8243''8658''8804'_6224 v0 v2
du_'8804''8243''8658''8804'_6224 ::
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''8243''8658''8804'_6224 v0 v1
  = coe seq (coe v1) (coe du_m'8804'm'43'n_3482 (coe v0))
-- Data.Nat.Properties.≤″-proof
d_'8804''8243''45'proof_6232 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8243''45'proof_6232 = erased
-- Data.Nat.Properties.m≤n⇒∃[o]m+o≡n
d_m'8804'n'8658''8707''91'o'93'm'43'o'8801'n_6238 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_m'8804'n'8658''8707''91'o'93'm'43'o'8801'n_6238 v0 v1 ~v2
  = du_m'8804'n'8658''8707''91'o'93'm'43'o'8801'n_6238 v0 v1
du_m'8804'n'8658''8707''91'o'93'm'43'o'8801'n_6238 ::
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_m'8804'n'8658''8707''91'o'93'm'43'o'8801'n_6238 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1 v0) erased
-- Data.Nat.Properties.guarded-∸≗∸
d_guarded'45''8760''8791''8760'_6250 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_guarded'45''8760''8791''8760'_6250 = erased
-- Data.Nat.Properties.m<ᵇn⇒1+m+[n-1+m]≡n
d_m'60''7495'n'8658'1'43'm'43''91'n'45'1'43'm'93''8801'n_6258 ::
  Integer ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'60''7495'n'8658'1'43'm'43''91'n'45'1'43'm'93''8801'n_6258
  = erased
-- Data.Nat.Properties.m<ᵇ1+m+n
d_m'60''7495'1'43'm'43'n_6270 :: Integer -> Integer -> AgdaAny
d_m'60''7495'1'43'm'43'n_6270 v0 ~v1
  = du_m'60''7495'1'43'm'43'n_6270 v0
du_m'60''7495'1'43'm'43'n_6270 :: Integer -> AgdaAny
du_m'60''7495'1'43'm'43'n_6270 v0
  = coe
      du_'60''8658''60''7495'_2728
      (coe
         du_m'8804'm'43'n_3482 (coe addInt (coe (1 :: Integer)) (coe v0)))
-- Data.Nat.Properties.<ᵇ⇒<″
d_'60''7495''8658''60''8243'_6274 ::
  Integer ->
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26
d_'60''7495''8658''60''8243'_6274 v0 v1 ~v2
  = du_'60''7495''8658''60''8243'_6274 v0 v1
du_'60''7495''8658''60''8243'_6274 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26
du_'60''7495''8658''60''8243'_6274 v0 v1
  = coe
      d_'60''8658''60''8243'_6222 v0 v1
      (coe du_'60''7495''8658''60'_2716 (coe v0))
-- Data.Nat.Properties.<″⇒<ᵇ
d_'60''8243''8658''60''7495'_6284 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26 ->
  AgdaAny
d_'60''8243''8658''60''7495'_6284 v0 ~v1 v2
  = du_'60''8243''8658''60''7495'_6284 v0 v2
du_'60''8243''8658''60''7495'_6284 ::
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26 ->
  AgdaAny
du_'60''8243''8658''60''7495'_6284 v0 v1
  = coe
      seq (coe v1)
      (coe
         du_'60''8658''60''7495'_2728
         (coe
            du_m'8804'm'43'n_3482 (coe addInt (coe (1 :: Integer)) (coe v0))))
-- Data.Nat.Properties._<″?_
d__'60''8243''63'__6290 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''8243''63'__6290 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
      (\ v2 -> coe du_'60''7495''8658''60''8243'_6274 (coe v0) (coe v1))
      (coe du_'60''8243''8658''60''7495'_6284 (coe v0))
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_66
         (coe ltInt (coe v0) (coe v1)))
-- Data.Nat.Properties._≤″?_
d__'8804''8243''63'__6296 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''8243''63'__6296 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe
                   MAlonzo.Code.Algebra.Definitions.RawMagma.C__'44'__40 (coe v1)
                   erased))
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe d__'60''8243''63'__6290 (coe v2) (coe v1))
-- Data.Nat.Properties._≥″?_
d__'8805''8243''63'__6304 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8805''8243''63'__6304 v0 v1
  = coe d__'8804''8243''63'__6296 (coe v1) (coe v0)
-- Data.Nat.Properties._>″?_
d__'62''8243''63'__6306 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'62''8243''63'__6306 v0 v1
  = coe d__'60''8243''63'__6290 (coe v1) (coe v0)
-- Data.Nat.Properties.≤″-irrelevant
d_'8804''8243''45'irrelevant_6308 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26 ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8243''45'irrelevant_6308 = erased
-- Data.Nat.Properties.<″-irrelevant
d_'60''8243''45'irrelevant_6322 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26 ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8243''45'irrelevant_6322 = erased
-- Data.Nat.Properties.>″-irrelevant
d_'62''8243''45'irrelevant_6324 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26 ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'62''8243''45'irrelevant_6324 = erased
-- Data.Nat.Properties.≥″-irrelevant
d_'8805''8243''45'irrelevant_6326 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26 ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8805''8243''45'irrelevant_6326 = erased
-- Data.Nat.Properties.≤‴⇒≤″
d_'8804''8244''8658''8804''8243'_6332 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__408 ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26
d_'8804''8244''8658''8804''8243'_6332 ~v0 ~v1 v2
  = du_'8804''8244''8658''8804''8243'_6332 v2
du_'8804''8244''8658''8804''8243'_6332 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__408 ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26
du_'8804''8244''8658''8804''8243'_6332 v0
  = case coe v0 of
      MAlonzo.Code.Data.Nat.Base.C_'8804''8244''45'refl_412
        -> coe
             MAlonzo.Code.Algebra.Definitions.RawMagma.C__'44'__40
             (coe (0 :: Integer)) erased
      MAlonzo.Code.Data.Nat.Base.C_'8804''8244''45'step_418 v3
        -> coe
             MAlonzo.Code.Algebra.Definitions.RawMagma.C__'44'__40
             (coe
                addInt (coe (1 :: Integer))
                (coe
                   MAlonzo.Code.Algebra.Definitions.RawMagma.d_quotient_36
                   (coe du_'8804''8244''8658''8804''8243'_6332 (coe v3))))
             erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.m≤‴m+k
d_m'8804''8244'm'43'k_6346 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__408
d_m'8804''8244'm'43'k_6346 ~v0 ~v1 v2 ~v3
  = du_m'8804''8244'm'43'k_6346 v2
du_m'8804''8244'm'43'k_6346 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__408
du_m'8804''8244'm'43'k_6346 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Nat.Base.C_'8804''8244''45'refl_412
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Nat.Base.C_'8804''8244''45'step_418
                (coe du_m'8804''8244'm'43'k_6346 (coe v1)))
-- Data.Nat.Properties.≤″⇒≤‴
d_'8804''8243''8658''8804''8244'_6362 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__408
d_'8804''8243''8658''8804''8244'_6362 ~v0 ~v1 v2
  = du_'8804''8243''8658''8804''8244'_6362 v2
du_'8804''8243''8658''8804''8244'_6362 ::
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__408
du_'8804''8243''8658''8804''8244'_6362 v0
  = coe
      du_m'8804''8244'm'43'k_6346
      (coe
         MAlonzo.Code.Algebra.Definitions.RawMagma.d_quotient_36 (coe v0))
-- Data.Nat.Properties.0≤‴n
d_0'8804''8244'n_6366 ::
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__408
d_0'8804''8244'n_6366 v0 = coe du_m'8804''8244'm'43'k_6346 (coe v0)
-- Data.Nat.Properties.<ᵇ⇒<‴
d_'60''7495''8658''60''8244'_6368 ::
  Integer ->
  Integer ->
  AgdaAny -> MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__408
d_'60''7495''8658''60''8244'_6368 v0 v1 ~v2
  = du_'60''7495''8658''60''8244'_6368 v0 v1
du_'60''7495''8658''60''8244'_6368 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__408
du_'60''7495''8658''60''8244'_6368 v0 v1
  = coe
      du_'8804''8243''8658''8804''8244'_6362
      (coe du_'60''7495''8658''60''8243'_6274 (coe v0) (coe v1))
-- Data.Nat.Properties.<‴⇒<ᵇ
d_'60''8244''8658''60''7495'_6376 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__408 -> AgdaAny
d_'60''8244''8658''60''7495'_6376 v0 ~v1 v2
  = du_'60''8244''8658''60''7495'_6376 v0 v2
du_'60''8244''8658''60''7495'_6376 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__408 -> AgdaAny
du_'60''8244''8658''60''7495'_6376 v0 v1
  = coe
      du_'60''8243''8658''60''7495'_6284 (coe v0)
      (coe du_'8804''8244''8658''8804''8243'_6332 (coe v1))
-- Data.Nat.Properties._<‴?_
d__'60''8244''63'__6380 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''8244''63'__6380 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
      (\ v2 -> coe du_'60''7495''8658''60''8244'_6368 (coe v0) (coe v1))
      (coe du_'60''8244''8658''60''7495'_6376 (coe v0))
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_66
         (coe ltInt (coe v0) (coe v1)))
-- Data.Nat.Properties._≤‴?_
d__'8804''8244''63'__6386 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''8244''63'__6386 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe d_0'8804''8244'n_6366 (coe v1)))
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe d__'60''8244''63'__6380 (coe v2) (coe v1))
-- Data.Nat.Properties._≥‴?_
d__'8805''8244''63'__6394 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8805''8244''63'__6394 v0 v1
  = coe d__'8804''8244''63'__6386 (coe v1) (coe v0)
-- Data.Nat.Properties._>‴?_
d__'62''8244''63'__6396 ::
  Integer ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'62''8244''63'__6396 v0 v1
  = coe d__'60''8244''63'__6380 (coe v1) (coe v0)
-- Data.Nat.Properties.≤⇒≤‴
d_'8804''8658''8804''8244'_6398 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__408
d_'8804''8658''8804''8244'_6398 v0 v1 ~v2
  = du_'8804''8658''8804''8244'_6398 v0 v1
du_'8804''8658''8804''8244'_6398 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__408
du_'8804''8658''8804''8244'_6398 v0 v1
  = coe
      du_'8804''8243''8658''8804''8244'_6362
      (coe du_'8804''8658''8804''8243'_6218 (coe v0) (coe v1))
-- Data.Nat.Properties.≤‴⇒≤
d_'8804''8244''8658''8804'_6400 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__408 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''8244''8658''8804'_6400 v0 ~v1 v2
  = du_'8804''8244''8658''8804'_6400 v0 v2
du_'8804''8244''8658''8804'_6400 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8244'__408 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''8244''8658''8804'_6400 v0 v1
  = coe
      du_'8804''8243''8658''8804'_6224 (coe v0)
      (coe du_'8804''8244''8658''8804''8243'_6332 (coe v1))
-- Data.Nat.Properties.eq?
d_eq'63'_6406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_eq'63'_6406 ~v0 ~v1 v2 = du_eq'63'_6406 v2
du_eq'63'_6406 ::
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_eq'63'_6406 v0
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.du_via'45'injection_160
      (coe v0) (coe d__'8799'__2688)
-- Data.Nat.Properties._.anyUpTo?
d_anyUpTo'63'_6424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) ->
  (Integer ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_anyUpTo'63'_6424 ~v0 ~v1 v2 v3 = du_anyUpTo'63'_6424 v2 v3
du_anyUpTo'63'_6424 ::
  (Integer ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_anyUpTo'63'_6424 v0 v1
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v3 = coe v0 v2 in
              coe
                (let v4 = coe du_anyUpTo'63'_6424 (coe v0) (coe v2) in
                 coe
                   (let v5
                          = case coe v4 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                                -> coe
                                     seq (coe v5)
                                     (case coe v6 of
                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                                          -> case coe v7 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                                 -> coe
                                                      seq (coe v9)
                                                      (coe
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                                                         (coe v6))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError in
                    coe
                      (case coe v3 of
                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                           -> let v8
                                    = case coe v4 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                          -> case coe v8 of
                                               MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                 -> case coe v9 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                                                        -> case coe v10 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                               -> coe seq (coe v12) (coe v4)
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> coe v5
                                               _ -> coe v5
                                        _ -> MAlonzo.RTE.mazUnreachableError in
                              coe
                                (if coe v6
                                   then let v9
                                              = case coe v4 of
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                                    -> case coe v9 of
                                                         MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                           -> case coe v10 of
                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                                                                  -> case coe v11 of
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                         -> coe
                                                                              seq (coe v13) (coe v4)
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> coe v8
                                                         _ -> coe v8
                                                  _ -> MAlonzo.RTE.mazUnreachableError in
                                        coe
                                          (case coe v7 of
                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v10
                                               -> coe
                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                    (coe v6)
                                                    (coe
                                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe v2)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe d_'8804''45'refl_2776 (coe v1))
                                                             (coe v10))))
                                             _ -> coe v9)
                                   else (case coe v4 of
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                             -> if coe v9
                                                  then case coe v10 of
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                                                           -> case coe v11 of
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                  -> coe seq (coe v13) (coe v4)
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> coe v8
                                                  else (case coe v7 of
                                                          MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                            -> case coe v10 of
                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                   -> coe
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                        (coe v9)
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                 _ -> coe v8
                                                          _ -> coe v8)
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                         _ -> MAlonzo.RTE.mazUnreachableError))))
-- Data.Nat.Properties._._.¬Pn<1+v
d_'172'Pn'60'1'43'v_6458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) ->
  (Integer ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172'Pn'60'1'43'v_6458 = erased
-- Data.Nat.Properties._.allUpTo?
d_allUpTo'63'_6488 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) ->
  (Integer ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_allUpTo'63'_6488 ~v0 ~v1 v2 v3 = du_allUpTo'63'_6488 v2 v3
du_allUpTo'63'_6488 ::
  (Integer ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_allUpTo'63'_6488 v0 v1
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (let v3 = coe v0 v2 in
              coe
                (let v4 = coe du_allUpTo'63'_6488 (coe v0) (coe v2) in
                 coe
                   (let v5
                          = case coe v4 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                                -> coe
                                     seq (coe v5)
                                     (coe
                                        seq (coe v6)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                           (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                                           (coe
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)))
                              _ -> MAlonzo.RTE.mazUnreachableError in
                    coe
                      (case coe v3 of
                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                           -> let v8
                                    = case coe v4 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                          -> case coe v8 of
                                               MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                 -> case coe v9 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                        -> coe
                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                             (coe v8)
                                                             (coe
                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                      _ -> coe v5
                                               _ -> coe v5
                                        _ -> MAlonzo.RTE.mazUnreachableError in
                              coe
                                (if coe v6
                                   then case coe v4 of
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                            -> if coe v9
                                                 then case coe v7 of
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                                                          -> case coe v10 of
                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                                                 -> coe
                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                      (coe v9)
                                                                      (coe
                                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                         (coe
                                                                            du_Pn'60'1'43'v_6520
                                                                            (coe v2) (coe v11)
                                                                            (coe v12)))
                                                               _ -> coe v8
                                                        _ -> coe v8
                                                 else (case coe v10 of
                                                         MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                           -> coe
                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                (coe v9)
                                                                (coe
                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                         _ -> coe v8)
                                          _ -> MAlonzo.RTE.mazUnreachableError
                                   else (let v9
                                               = case coe v4 of
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                                     -> case coe v9 of
                                                          MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                            -> case coe v10 of
                                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                   -> coe
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                        (coe v9)
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                                                 _ -> coe v8
                                                          _ -> coe v8
                                                   _ -> MAlonzo.RTE.mazUnreachableError in
                                         coe
                                           (case coe v7 of
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                -> coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v6)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
                                              _ -> coe v9)))
                         _ -> MAlonzo.RTE.mazUnreachableError))))
-- Data.Nat.Properties._._.Pn<1+v
d_Pn'60'1'43'v_6520 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) ->
  (Integer ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny) ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_Pn'60'1'43'v_6520 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_Pn'60'1'43'v_6520 v3 v4 v5 v6 v7
du_Pn'60'1'43'v_6520 ::
  Integer ->
  AgdaAny ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny) ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
du_Pn'60'1'43'v_6520 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v7
        -> let v8
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
                     erased (\ v8 -> coe du_'8801''8658''8801''7495'_2678 (coe v3))
                     (coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_66
                        (coe eqInt (coe v3) (coe v0))) in
           coe
             (case coe v8 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                  -> if coe v9
                       then coe seq (coe v10) (coe v1)
                       else coe
                              seq (coe v10)
                              (coe
                                 v2 v3 (coe du_'8804''8743''8802''8658''60'_2918 (coe v0) (coe v7)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Properties.∀[m≤n⇒m≢o]⇒o<n
d_'8704''91'm'8804'n'8658'm'8802'o'93''8658'o'60'n_6546 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8704''91'm'8804'n'8658'm'8802'o'93''8658'o'60'n_6546 v0 v1 v2
  = coe
      du_'8704''91'm'8804'n'8658'm'8802'o'93''8658'n'60'o_3132 v0 v1
-- Data.Nat.Properties.∀[m<n⇒m≢o]⇒o≤n
d_'8704''91'm'60'n'8658'm'8802'o'93''8658'o'8804'n_6554 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8704''91'm'60'n'8658'm'8802'o'93''8658'o'8804'n_6554 v0 v1 v2
  = coe
      du_'8704''91'm'60'n'8658'm'8802'o'93''8658'n'8804'o_3160 v0 v1
-- Data.Nat.Properties.*-+-isSemiring
d_'42''45''43''45'isSemiring_6556 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1570
d_'42''45''43''45'isSemiring_6556
  = coe d_'43''45''42''45'isSemiring_3754
-- Data.Nat.Properties.*-+-isCommutativeSemiring
d_'42''45''43''45'isCommutativeSemiring_6558 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1678
d_'42''45''43''45'isCommutativeSemiring_6558
  = coe d_'43''45''42''45'isCommutativeSemiring_3756
-- Data.Nat.Properties.*-+-semiring
d_'42''45''43''45'semiring_6560 ::
  MAlonzo.Code.Algebra.Bundles.T_Semiring_2280
d_'42''45''43''45'semiring_6560
  = coe d_'43''45''42''45'semiring_3768
-- Data.Nat.Properties.*-+-commutativeSemiring
d_'42''45''43''45'commutativeSemiring_6562 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemiring_2446
d_'42''45''43''45'commutativeSemiring_6562
  = coe d_'43''45''42''45'commutativeSemiring_3770
-- Data.Nat.Properties.∣m+n-m+o∣≡∣n-o|
d_'8739'm'43'n'45'm'43'o'8739''8801''8739'n'45'o'124'_6564 ::
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'm'43'n'45'm'43'o'8739''8801''8739'n'45'o'124'_6564 = erased
-- Data.Nat.Properties.m≤n⇒n⊔m≡n
d_m'8804'n'8658'n'8852'm'8801'n_6566 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8804'n'8658'n'8852'm'8801'n_6566 = erased
-- Data.Nat.Properties.m≤n⇒n⊓m≡m
d_m'8804'n'8658'n'8851'm'8801'm_6568 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_m'8804'n'8658'n'8851'm'8801'm_6568 = erased
-- Data.Nat.Properties.n⊔m≡m⇒n≤m
d_n'8852'm'8801'm'8658'n'8804'm_6570 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'8852'm'8801'm'8658'n'8804'm_6570
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3100
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.n⊔m≡n⇒m≤n
d_n'8852'm'8801'n'8658'm'8804'n_6572 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'8852'm'8801'n'8658'm'8804'n_6572
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3068
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.n≤m⊔n
d_n'8804'm'8852'n_6574 ::
  Integer -> Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_n'8804'm'8852'n_6574
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2834
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊔-least
d_'8852''45'least_6576 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8852''45'least_6576
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3278
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-greatest
d_'8851''45'greatest_6578 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8851''45'greatest_6578
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3278
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊔-pres-≤m
d_'8852''45'pres'45''8804'm_6580 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8852''45'pres'45''8804'm_6580
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8852''45'operator_4440 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3278
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_746
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_174
               (coe v1))))
-- Data.Nat.Properties.⊓-pres-m≤
d_'8851''45'pres'45'm'8804'_6582 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8851''45'pres'45'm'8804'_6582
  = let v0 = d_'8804''45'totalPreorder_2822 in
    coe
      (let v1 = d_'8851''45'operator_4438 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3278
            (coe v0) (coe v1)))
-- Data.Nat.Properties.⊔-abs-⊓
d_'8852''45'abs'45''8851'_6584 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8852''45'abs'45''8851'_6584 = erased
-- Data.Nat.Properties.⊓-abs-⊔
d_'8851''45'abs'45''8852'_6586 ::
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8851''45'abs'45''8852'_6586 = erased
-- Data.Nat.Properties.suc[pred[n]]≡n
d_suc'91'pred'91'n'93''93''8801'n_6588 ::
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_suc'91'pred'91'n'93''93''8801'n_6588 = erased
-- Data.Nat.Properties.≤-step
d_'8804''45'step_6594 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'step_6594 ~v0 ~v1 v2 = du_'8804''45'step_6594 v2
du_'8804''45'step_6594 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'step_6594 v0 = coe v0
-- Data.Nat.Properties.≤-stepsˡ
d_'8804''45'steps'737'_6596 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'steps'737'_6596 ~v0 ~v1 ~v2 v3
  = du_'8804''45'steps'737'_6596 v3
du_'8804''45'steps'737'_6596 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'steps'737'_6596 v0 = coe v0
-- Data.Nat.Properties.≤-stepsʳ
d_'8804''45'steps'691'_6598 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'8804''45'steps'691'_6598 ~v0 ~v1 ~v2 v3
  = du_'8804''45'steps'691'_6598 v3
du_'8804''45'steps'691'_6598 ::
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_'8804''45'steps'691'_6598 v0 = coe v0
-- Data.Nat.Properties.<-step
d_'60''45'step_6600 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'step_6600 v0 v1 v2
  = coe du_m'60'n'8658'm'60'1'43'n_3062 v2
-- Data.Nat.Properties.pred-mono
d_pred'45'mono_6602 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_pred'45'mono_6602 v0 v1 v2
  = coe du_pred'45'mono'45''8804'_5676 v0 v2
-- Data.Nat.Properties.<-transʳ
d_'60''45'trans'691'_6604 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'trans'691'_6604 v0 v1 v2 v3 v4
  = coe du_'8804''45''60''45'trans_2986 v3 v4
-- Data.Nat.Properties.<-transˡ
d_'60''45'trans'737'_6606 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'trans'737'_6606 v0 v1 v2 v3 v4
  = coe du_'60''45''8804''45'trans_2992 v3 v4
