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

module MAlonzo.Code.FinSet where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base

-- FinSet._∈_
d__'8712'__10 a0 a1 a2 a3 = ()
data T__'8712'__10
  = C_here_18 | C_left_26 [AgdaAny] [AgdaAny] T__'8712'__10 |
    C_right_34 [AgdaAny] [AgdaAny] T__'8712'__10
-- FinSet._⊆_
d__'8838'__44 a0 a1 a2 a3 = ()
data T__'8838'__44
  = C_non_52 | C_addl_62 [AgdaAny] [AgdaAny] AgdaAny T__'8838'__44 |
    C_addr_64
-- FinSet.congm
d_congm_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  AgdaAny ->
  [AgdaAny] -> (AgdaAny -> AgdaAny) -> T__'8712'__10 -> T__'8712'__10
d_congm_80 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_congm_80 v5 v6
du_congm_80 ::
  (AgdaAny -> AgdaAny) -> T__'8712'__10 -> T__'8712'__10
du_congm_80 v0 v1
  = case coe v1 of
      C_here_18 -> coe v1
      C_left_26 v2 v3 v4
        -> coe
             C_left_26
             (coe MAlonzo.Code.Data.List.Base.du_map_22 (coe v0) (coe v2))
             (coe MAlonzo.Code.Data.List.Base.du_map_22 (coe v0) (coe v3))
             (coe du_congm_80 (coe v0) (coe v4))
      C_right_34 v2 v3 v4
        -> coe
             C_right_34
             (coe MAlonzo.Code.Data.List.Base.du_map_22 (coe v0) (coe v2))
             (coe MAlonzo.Code.Data.List.Base.du_map_22 (coe v0) (coe v3))
             (coe du_congm_80 (coe v0) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- FinSet.substm
d_substm_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'8712'__10 -> T__'8712'__10
d_substm_118 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_substm_118 v6
du_substm_118 :: T__'8712'__10 -> T__'8712'__10
du_substm_118 v0 = coe v0
-- FinSet.FinSet
d_FinSet_124 a0 = ()
data T_FinSet_124
  = C_FinSet'46'constructor_8803 [AgdaAny] (AgdaAny -> T__'8712'__10)
                                 ([AgdaAny] ->
                                  (AgdaAny -> T__'8712'__10) ->
                                  MAlonzo.Code.Data.Nat.Base.T__'8804'__22)
-- FinSet.FinSet.Carrier
d_Carrier_142 :: T_FinSet_124 -> ()
d_Carrier_142 = erased
-- FinSet.FinSet.list
d_list_144 :: T_FinSet_124 -> [AgdaAny]
d_list_144 v0
  = case coe v0 of
      C_FinSet'46'constructor_8803 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- FinSet.FinSet.proof
d_proof_148 :: T_FinSet_124 -> AgdaAny -> T__'8712'__10
d_proof_148 v0
  = case coe v0 of
      C_FinSet'46'constructor_8803 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- FinSet.FinSet.minimal
d_minimal_154 ::
  T_FinSet_124 ->
  [AgdaAny] ->
  (AgdaAny -> T__'8712'__10) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_minimal_154 v0
  = case coe v0 of
      C_FinSet'46'constructor_8803 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- FinSet.nonept
d_nonept_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  [AgdaAny] ->
  T__'8712'__10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_nonept_164 = erased
-- FinSet.L
d_L_172 :: Integer -> [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_L_172 v0
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                (coe
                   MAlonzo.Code.Data.List.Base.du_map_22
                   (coe MAlonzo.Code.Data.Fin.Base.C_suc_16) (coe d_L_172 (coe v1))))
-- FinSet.P
d_P_180 ::
  Integer -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T__'8712'__10
d_P_180 v0
  = case coe v0 of
      0 -> erased
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                (\ v2 ->
                   case coe v2 of
                     MAlonzo.Code.Data.Fin.Base.C_zero_12
                       -> coe
                            C_left_26
                            (coe
                               MAlonzo.Code.Data.List.Base.du_'91'_'93'_286
                               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                            (coe
                               MAlonzo.Code.Data.List.Base.du_map_22
                               (coe MAlonzo.Code.Data.Fin.Base.C_suc_16) (coe d_L_172 (coe v1)))
                            (coe C_here_18)
                     MAlonzo.Code.Data.Fin.Base.C_suc_16 v4
                       -> coe
                            C_right_34
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                            (coe
                               MAlonzo.Code.Data.List.Base.du_map_22
                               (coe MAlonzo.Code.Data.Fin.Base.C_suc_16) (coe d_L_172 (coe v1)))
                            (coe
                               du_congm_80 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16)
                               (coe d_P_180 v1 v4))
                     _ -> MAlonzo.RTE.mazUnreachableError))
-- FinSet.M
d_M_194 ::
  Integer ->
  [MAlonzo.Code.Data.Fin.Base.T_Fin_10] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T__'8712'__10) ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_M_194 v0
  = case coe v0 of
      0 -> coe (\ v1 v2 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      _ -> coe
             (\ v1 ->
                case coe v1 of
                  []
                    -> coe (\ v2 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_14)
                  (:) v2 v3
                    -> coe (\ v4 -> MAlonzo.RTE.mazHole "_235@15806297461337506466")
                  _ -> MAlonzo.RTE.mazUnreachableError)
-- FinSet.F
d_F_210 :: Integer -> T_FinSet_124
d_F_210 v0
  = coe
      C_FinSet'46'constructor_8803 (d_L_172 (coe v0)) (d_P_180 (coe v0))
      (MAlonzo.RTE.mazHole "_238@15806297461337506466")
