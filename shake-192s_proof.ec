require import AllCore IntDiv CoreMap List Distr.

require import SPX_Safety.

from Jasmin require import Jcheck JSafety JWord.

exception Safty.

(* The post and trace are valid. *)

(* Auxiliary Lemmas *)

lemma BBAnd_big_foldr ['a] (F : 'a -> bool) (r : 'a list) :
  foldr (fun x0 acc => x0 /\ acc) true (map F r) =
  StdBigop.Bigbool.BBAnd.big predT F r.
    proof.
by rewrite /StdBigop.Bigbool.BBAnd.big filter_predT.
  qed.

lemma and_iota (F : int -> bool) i l :
  foldr (fun x0 acc => x0 /\ acc) true (map F (iota_ i l)) <=>
  forall k, i <= k < i + l => F k.
    proof.
      rewrite BBAnd_big_foldr StdBigop.Bigbool.BBAnd.bigP filter_predT List.allP.
    smt(mem_iota).
  qed.

(* Main Lemmas *)

lemma __adrs_to_bytes_proof _bytes _b_bytes _adrs _b_adrs :
      (__adrs_to_bytes_spec _bytes _b_bytes _adrs _b_adrs).
proof.
rewrite /__adrs_to_bytes_spec .
proc; auto .
while (0 <= (8*i) /\ BArray32.is_init b_bytes 0 (i*4)).
  auto .
  rewrite /is_init .
smt().
  auto .
smt().
qed .

lemma __adrs_init_proof _adrs _b_adrs : (__adrs_init_spec _adrs _b_adrs).
proof.
rewrite /__adrs_init_spec .
proc; auto .
while (0 <= i*8 /\ BArray32.is_init b_adrs 0 (i*8)).
auto .
  rewrite /is_init /= => /> *.
split.
  smt().
smt().
wp.
skip.
  rewrite /is_init /= .
smt().
qed .

lemma __adrs_clone_proof _adrs_new _b_adrs_new _adrs _b_adrs :
      (__adrs_clone_spec _adrs_new _b_adrs_new _adrs _b_adrs).
proof.
rewrite /__adrs_clone_spec .
proc; auto .
while (0 <= i*8 /\ BArray32.is_init b_adrs_new 0 (i*8)).
auto .
  rewrite /is_init /= => /> *.
split.
smt().
  smt().
  wp.
  skip.
smt().
qed .

lemma __adrs_compress_proof _out _b_out _adrs _b_adrs :
      (__adrs_compress_spec _out _b_out _adrs _b_adrs).
proof.
rewrite /__adrs_compress_spec .
proc; auto .
while (0 <= i*8 /\ (forall (k: int), 0 <= k /\ k <= i => BArray22."_.[_]" b_out (k+9) = JWord.W8.of_int 255) /\ (forall (k: int), 0 <= k /\ k <= 8 => BArray22."_.[_]" b_out k = JWord.W8.of_int 255)).
auto .
  rewrite /is_init /= => /> *.
split.
  smt().
  progress.
smt().
smt().
smt().
  auto.
  smt(BArray22.get_setE).
  auto.
  smt(BArray22.get_setE).
auto.
while (0 <= i*8 /\ (forall (k: int), 0 <= k /\ k <= i => BArray22."_.[_]" b_out k = JWord.W8.of_int 255) /\ BArray22."_.[_]" b_out 0 = JWord.W8.of_int 255).
  wp.
  skip.
move => &hr.
  rewrite /= => /> *.
split.
  smt().
  rewrite /= => /> *.
  split.
  smt().
move => *.
  split.
  smt().
  rewrite /= => /> *.
  split.
move => k.
case(k = i{hr}+1).
move => *.
subst.
  smt(BArray22.get_setE).
  smt(BArray22.get_setE).
  smt(BArray22.get_setE).
auto.
ecall (__adrs_to_bytes_proof param_0 b_param param (BArray32.init_arr
    (JWord.W8.of_int 255))).
wp.
skip.
      rewrite /= => /> *.
split.
      smt(BArray32.init_arrP BArray24.init_arrP).
rewrite /= => /> *.
      split.
      smt(BArray22.get_setE).
      rewrite /= => /= *.
split.
      smt(BArray22.get_setE).
      rewrite /= => /= *.
smt().
qed.


lemma __adrs_set_layer_addr_proof _adrs _b_adrs _layer :
      (__adrs_set_layer_addr_spec _adrs _b_adrs _layer).
proof.
rewrite /__adrs_set_layer_addr_spec .
proc; auto .
rewrite /is_init /valid /= .
smt(BArray32.init_arrP BArray24.init_arrP).
qed .

lemma __adrs_set_tree_addr_proof _adrs _b_adrs _tree _b_tree :
      (__adrs_set_tree_addr_spec _adrs _b_adrs _tree _b_tree).
proof.
rewrite /__adrs_set_tree_addr_spec .
proc; auto .
while (i < 3 => (0 <= (1+i)*4 /\ (1+i)*4 + 4 <= 32 /\ 0 <= i*4 /\ i*4 +4 <= 12)).
auto .
  rewrite /is_init /valid /= => /> *.
progress; smt().
auto .
  rewrite /is_init /= => /> * .
smt(BArray32.initE BArray24.initE).
qed .

lemma __adrs_set_type_and_clear_proof _adrs _b_adrs _t :
      (__adrs_set_type_and_clear_spec _adrs _b_adrs _t).
proof.
rewrite /__adrs_set_type_and_clear_spec .
proc; auto .
while (i <= 2 /\ i < 4 => (0 <= i*8 /\ i*8 + 8 <= 32)).
auto .
rewrite /= => /> *.
  smt().
auto .
rewrite /valid /= => /> * .
smt(BArray32.initE BArray24.initE).
qed .

lemma __adrs_set_key_pair_addr_proof _adrs _b_adrs _keypair :
      (__adrs_set_key_pair_addr_spec _adrs _b_adrs _keypair).
proof.
rewrite /__adrs_set_key_pair_addr_spec .
proc; auto .
rewrite /is_init /valid /= .
smt(BArray32.init_arrP BArray24.init_arrP).
qed .

lemma __adrs_set_chain_addr_proof _adrs _b_adrs _chain :
      (__adrs_set_chain_addr_spec _adrs _b_adrs _chain).
proof.
rewrite /__adrs_set_chain_addr_spec .
proc; auto .
rewrite /is_init /valid /= .
smt(BArray32.init_arrP BArray24.init_arrP).
qed .

lemma __adrs_set_tree_height_proof _adrs _b_adrs _height :
      (__adrs_set_tree_height_spec _adrs _b_adrs _height).
proof.
rewrite /__adrs_set_tree_height_spec .
proc; auto .
rewrite /is_init /valid /= .
smt(BArray32.init_arrP BArray24.init_arrP).
qed .

lemma __adrs_set_hash_addr_proof _adrs _b_adrs _hashaddr :
      (__adrs_set_hash_addr_spec _adrs _b_adrs _hashaddr).
proof.
rewrite /__adrs_set_hash_addr_spec .
proc; auto .
rewrite /is_init /valid /= .
smt(BArray32.init_arrP BArray24.init_arrP).
qed .

lemma __adrs_set_tree_index_proof _adrs _b_adrs _treeindex :
      (__adrs_set_tree_index_spec _adrs _b_adrs _treeindex).
proof.
rewrite /__adrs_set_tree_index_spec .
proc; auto .
rewrite /is_init /valid /= .
smt(BArray32.init_arrP BArray24.init_arrP).
qed .

lemma __adrs_get_key_pair_addr_proof _adrs _b_adrs :
      (__adrs_get_key_pair_addr_spec _adrs _b_adrs).
proof.
rewrite /__adrs_get_key_pair_addr_spec .
proc; auto .
qed .

lemma __adrs_get_tree_index_proof _adrs _b_adrs :
      (__adrs_get_tree_index_spec _adrs _b_adrs).
proof.
rewrite /__adrs_get_tree_index_spec .
proc; auto .
qed .

lemma __SHLQ_proof _x _shbytes : (__SHLQ_spec _x _shbytes).
proof.
rewrite /__SHLQ_spec .
proc; auto .
qed .

lemma __SHLDQ_proof _x _shbytes : (__SHLDQ_spec _x _shbytes).
proof.
rewrite /__SHLDQ_spec .
proc; auto .
qed .

lemma __SHLQ_256_proof _x _shbytes : (__SHLQ_256_spec _x _shbytes).
proof.
rewrite /__SHLQ_256_spec .
proc; auto .
qed .

lemma __ANDN_64_proof _a _b : (__ANDN_64_spec _a _b).
proof.
rewrite /__ANDN_64_spec .
proc; auto .
qed .

lemma keccakf1600_index_proof _x _y : (keccakf1600_index_spec _x _y).
proof.
rewrite /keccakf1600_index_spec .
proc; auto .
qed .

lemma keccakf1600_rho_offsets_proof _i : (keccakf1600_rho_offsets_spec _i).
proof.
rewrite /keccakf1600_rho_offsets_spec .
proc; auto .
while (true).
auto .
wp.
skip.
smt().
qed .

lemma keccakf1600_rhotates_proof _x _y : (keccakf1600_rhotates_spec _x _y).
proof.
rewrite /keccakf1600_rhotates_spec .
proc; auto .
ecall (keccakf1600_rho_offsets_proof param_1).
auto .
ecall (keccakf1600_index_proof param_0 param).
auto .
qed .

lemma __rol_u64_ref_proof _x _i : (__rol_u64_ref_spec _x _i).
proof.
rewrite /__rol_u64_ref_spec .
proc; auto .
qed .

lemma __theta_sum_ref_proof _a _b_a : (__theta_sum_ref_spec _a _b_a).
proof.
rewrite /__theta_sum_ref_spec .
  proc; auto .
while (1 <= y /\ y <= 5 /\ BArray40.is_init b_c 0 40).
auto .
  while (0 <= x /\ y < 5 /\ (BArray40.is_init b_c 0 40) /\ ((x < 5) => (0 <= x*8 /\ x*8 + 8 <= 40
  /\ 0 <= (x + y * 5) * 8 /\ (x + y * 5) * 8 + 8 <= 200))).
auto .
  rewrite /is_init /= => /> *.
  split.
split.
smt().
smt().
  rewrite /= => /> *.
split.
  smt().
  rewrite /= => /> *.
split.
  smt().
progress; smt().
  auto .
  rewrite /= => /> *.
  progress; smt().
auto.
  while (0 <= x /\ (x < 5 => (0 <= x * 8 /\ x * 8 + 8 <= 40 /\ 0 <= x * 8 /\ x * 8 + 8 <= 200)) /\
         (forall (k: int), 0 <= k /\ k < 8*x => BArray40."_.[_]" b_c k = JWord.W8.of_int 255)).
auto .
  rewrite /= => /> *.
progress; smt(BArray40.is_init_cellP BArray40.is_init_cell_set64d).
auto .
rewrite /is_init /= => /> *.
smt().
qed .

lemma __theta_rol_ref_proof _c _b_c : (__theta_rol_ref_spec _c _b_c).
proof.
rewrite /__theta_rol_ref_spec .
proc; auto .
while (0 <= x /\ x <= 5 /\ (x < 5 => (0 <= x * 8 /\ x * 8 + 8 <= 40 /\
       0 <= (x + 1) %% 5 * 8 /\ (x + 1) %% 5 * 8 + 8 <= 40 /\
       0 <= (x - 1 + 5) %% 5 * 8 /\ (x - 1 + 5) %% 5 * 8 + 8 <= 40)) /\
       (forall (k: int), (0 <= k /\ k <= (x - 1)) => (BArray40.is_init b_d 0 (k * 8 + 8)))).
auto .
ecall (__rol_u64_ref_proof param_0 param).
auto .
rewrite /is_init /= => /> *.
smt().
auto .
rewrite /is_init /= => /> *.
split.
smt().
rewrite /BArray40.is_init_cell.
move => _d.
move => x.
move => ?.
move => ?.
move => ?.
move => H2xall.
rewrite /= => /> *.
have h := H2xall 4 _.
smt().
smt().
qed .

lemma __rol_sum_ref_proof _a _b_a _d _b_d _y :
      (__rol_sum_ref_spec _a _b_a _d _b_d _y).
proof.
rewrite /__rol_sum_ref_spec .
proc; auto.
while (0 <= x /\ x <= 5 /\ (x < 5 => (0 <= x * 8 /\ x * 8 + 8 <= 40)) /\
      (forall (k: int), (0 <= k /\ k <= (x - 1)) => (BArray40.is_init b_b 0 (k * 8 + 8)))).
auto .
ecall (__rol_u64_ref_proof param_2 param_1).
auto .
ecall (keccakf1600_rhotates_proof param_0 param).
         auto .
         rewrite /is_init /= => />.
     move => &hr.
     move => ?.
     move => ?.
     move => ?.
     move => H2xall.
     rewrite /= => /> *.
progress.
         smt().
         smt().
         smt().
         smt().
         smt().
         smt().
         smt().
         smt().
         smt().
        smt().
        case : (x{hr} * 8 <= i) => case1.
        smt().
        have := H2xall (x{hr} - 1) _.
        smt().
        smt().

         auto .
         rewrite /is_init /= => /> * .
         progress.
         smt().
     have x_val := H2 4 _.
         smt().
     smt().
qed .

lemma __set_row_ref_proof _e _b_e _b _b_b _y :
      (__set_row_ref_spec _e _b_e _b _b_b _y).
proof.
rewrite /__set_row_ref_spec .
proc; auto .
while (0 <= x /\ x <= 5 /\ (x < 5 => (0 <= x * 8 /\ x * 8 + 8 <= 40 /\ 0 <= (x + y * 5) * 8 /\
      (x + y * 5) * 8 + 8 <= 200)) /\
       BArray40.is_init b_b 0 40 /\ 0 <= y /\ y < 5 /\ BArray200.is_init b_e 0 (y * 5 * 8) /\
       (forall (j: int), (0 <= j /\ j <= (x - 1)) => (BArray200.is_init b_e 0 ((j + y * 5) * 8 + 8))) /\
      (forall (k: int), (0 <= k /\ k <= (x - 1)) => (BArray40.is_init b_b 0 (k * 8 + 8)))).
auto .
ecall (__ANDN_64_proof param_0 param).
        auto .
    rewrite /is_init /BArray40.is_init_cell /= => />.
    move => &hr.
    move => ?.
    move => ?.
    move => ?.
    move => ?.
    move => ?.
    move => ?.
    move => ?.
    move => H2xall.
        rewrite /= => /> *.
        progress.
        smt().
        smt().
        smt().
        smt().
        smt().
        smt().
        smt().
        smt().
        smt().
        smt().
        smt().
        smt().
        smt().
        smt().
        smt().

        case : ((x{hr} + y{hr} * 5) * 8 <= i) => case1.
        smt().
        case : (x{hr} = 0) => case2.
        smt().
        have := H2xall (x{hr} - 1) _.
        smt().
        smt().
        smt().

    auto.
        smt().
qed .

lemma _pround_ref_proof _e _b_e _a _b_a : (_pround_ref_spec _e _b_e _a _b_a).
proof.
rewrite /_pround_ref_spec .
proc; auto.
  while (0 <= y /\ y <= 5 /\
  ((1 <= y) => (BArray40.is_init b_result_0 0 40)) /\
  ((1 <= y) => (BArray200.is_init b_e 0 ((y - 1 + 1) * 5 * 8)))).
auto .
ecall (__set_row_ref_proof param_6 b_param param_5 (BArray40.init_arr
                                                   (JWord.W8.of_int 255)) param_4).
auto .
ecall (__rol_sum_ref_proof param_3 (BArray200.init_arr (JWord.W8.of_int 255)) 
       param_2 (BArray40.init_arr (JWord.W8.of_int 255)) param_1).
auto .
                                                     rewrite /is_init /= => />.
                                               progress.
                                                     smt(BArray40.init_arrP).
                                                     smt(BArray200.init_arrP).
                                                     smt().
                                                     smt().
                                                     smt().
                                               auto.
ecall (__theta_rol_ref_proof param_0 (BArray40.init_arr (JWord.W8.of_int 255))).
                                                 auto .
ecall (__theta_sum_ref_proof param (BArray200.init_arr (JWord.W8.of_int 255))).
auto .
                                                     rewrite /is_init /= => /> * .
                                               progress.
                                                     smt(BArray200.init_arrP).
                                                     smt(BArray40.init_arrP).
                                                 smt().
qed .

lemma __keccakf1600_ref_proof _a _b_a : (__keccakf1600_ref_spec _a _b_a).
proof.
rewrite /__keccakf1600_ref_spec .
proc; auto .
while (2 <= c /\ c <= 24 /\
      ((1 <= c) => (BArray200.is_init b_a 0 200))).
auto .
ecall (_pround_ref_proof param_2 b_param_0 param_1 b_param).
auto .
ecall (_pround_ref_proof param_0 b_param_1 param (BArray200.init_arr
                                                 (JWord.W8.of_int 255))).
auto .
rewrite /is_init /= => /> *.
smt(BArray200.init_arrP).
auto .
ecall (_pround_ref_proof param_2 b_param_0 param_1 b_param).
auto .
ecall (_pround_ref_proof param_0 b_param_1 param (BArray200.init_arr
                                                 (JWord.W8.of_int 255))).
auto .
rewrite /is_init /valid /= .
smt(BArray200.init_arrP).
qed .

lemma _keccakf1600_ref_proof _a _b_a : (_keccakf1600_ref_spec _a _b_a).
proof.
rewrite /_keccakf1600_ref_spec .
proc; auto .
ecall (__keccakf1600_ref_proof param (BArray200.init_arr (JWord.W8.of_int 255))).
auto .
rewrite /is_init /valid /= .
smt(BArray200.init_arrP).
qed .

lemma _keccakf1600_ref__proof _a _b_a : (_keccakf1600_ref__spec _a _b_a).
proof.
rewrite /_keccakf1600_ref__spec .
proc; auto .
ecall (_keccakf1600_ref_proof param (BArray200.init_arr (JWord.W8.of_int 255))).
auto .
rewrite /is_init /valid /= .
smt(BArray200.init_arrP).
qed .

lemma __state_init_ref_proof _st _b_st : (__state_init_ref_spec _st _b_st).
proof.
rewrite /__state_init_ref_spec .
proc; auto .
while (0 <= i /\ i <= 25 /\
       ((1 <= i) => (BArray200.is_init b_st 0 (i*8)))).
auto .
rewrite /is_init /= => /> *.
smt().
auto .
rewrite /is_init /= => /> *.
smt().
qed .

lemma __addratebit_ref_proof _st _b_st __RATE8 :
      (__addratebit_ref_spec _st _b_st __RATE8).
proof.
rewrite /__addratebit_ref_spec .
proc; auto .
rewrite /is_init /= => /> *.
smt(BArray200.init_arrP).
qed .

lemma __index_spec_proof _x _y : (__index_spec_spec _x _y).
proof.
rewrite /__index_spec_spec .
proc; auto .
qed .

lemma __keccak_rho_offsets_spec_proof _i :
      (__keccak_rho_offsets_spec_spec _i).
proof.
rewrite /__keccak_rho_offsets_spec_spec .
proc; auto .
while (0 <= t /\ t <= 24 /\ 0 <= r /\ r <= 63).
auto .
rewrite /= => /> *.
smt().
auto .
qed .

lemma __rhotates_spec_proof _x _y : (__rhotates_spec_spec _x _y).
proof.
rewrite /__rhotates_spec_spec .
proc; auto .
ecall (__keccak_rho_offsets_spec_proof param_1).
auto .
ecall (__index_spec_proof param_0 param).
auto .
qed .

lemma __rotate_left_64_proof _v _rOTATE_BY :
      (__rotate_left_64_spec _v _rOTATE_BY).
proof.
rewrite /__rotate_left_64_spec .
proc; auto .
qed .

lemma __theta_sum_ref1_proof _a _b_a : (__theta_sum_ref1_spec _a _b_a).
proof.
rewrite /__theta_sum_ref1_spec .
  proc; auto .
while (1 <= y /\ y <= 5 /\ BArray40.is_init b_c 0 40).
auto .
while (1 <= y /\ y < 5 /\
       0 <= x /\ x <= 5 /\  BArray40.is_init b_c 0 40).
auto .
rewrite /is_init /= => /> *.
smt().
auto .
rewrite /is_init /valid /=.
smt().
auto .
while (0 <= x /\ x <= 5 /\
      ((1 <= x) => (BArray40.is_init b_c 0 (x*8)))).
auto .
rewrite /is_init /= => /> *.
smt().
auto .
rewrite /is_init /= => /> *.
smt().
qed .

lemma __theta_rol_ref1_proof _c _b_c : (__theta_rol_ref1_spec _c _b_c).
proof.
rewrite /__theta_rol_ref1_spec .
proc; auto .
while (0 <= x /\ x <= 5 /\
      ((1 <= x) => (BArray40.is_init b_d 0 (x*8)))).
auto .
ecall (__rotate_left_64_proof param_0 param).
auto .
rewrite /is_init /valid /=.
smt().
auto .
rewrite /is_init /valid /= .
smt().
qed .

lemma __rol_sum_ref1_proof _a _b_a _d _b_d _y :
      (__rol_sum_ref1_spec _a _b_a _d _b_d _y).
proof.
rewrite /__rol_sum_ref1_spec .
proc; auto.
while (0 <= x /\ x <= 5 /\
  ((1 <= x) => (BArray40.is_init b_b 0 (x*8)))).
sp.
auto.
seq 1 : (true /\ true /\ 0 <= result /\ result <= 63 /\
        0 <= x /\ x < 5 /\ 0 <= x_ /\ x_ < 5 /\ 0 <= y_ /\ y_ < 5 /\
        ((1 <= x) => (BArray40.is_init b_b 0 (x*8)))).
ecall (__rhotates_spec_proof param_0 param).
          auto.
      smt().
        if.
        sp.
        if.
        if.
        sp.
        if.
        if.
        if.
        if.
        sp.
        if.
        if.
        if.
        if.
    auto.
ecall (__rotate_left_64_proof param_2 param_1).
auto .
          rewrite /is_init /= => /> *.
      smt().
          auto.
          ecall (__rotate_left_64_proof param_2 param_1).
          auto.
          smt(BArray40.is_init_cell_set64d).
          auto.
          ecall (__rotate_left_64_proof param_2 param_1).
          auto.
      smt().
          auto.
          ecall (__rotate_left_64_proof param_2 param_1).
          auto.
          smt().
          auto.
          smt(BArray40.is_init_cell_set64d).
          exfalso.
      smt().
          exfalso.
          smt(BArray40.is_init_cell_set64d).
          exfalso.
          smt().
          exfalso.
          smt().
          exfalso.
          smt().
          exfalso.
          smt().
          exfalso.
          smt().
          auto.
      smt().
qed .

lemma __set_row_ref1_proof _e _b_e _b _b_b _y _s_rc :
      (__set_row_ref1_spec _e _b_e _b _b_b _y _s_rc).
proof.
rewrite /__set_row_ref1_spec .
proc; auto.
while (0 <= x /\ x <= 5 /\ 0 <= y /\ y <= 4 /\ _y = y /\
       BArray200.is_init b_e 0 (_y * 40) /\
      ((1 <= x) => (BArray200.is_init b_e 0 (_y * 40 + x * 8)))).
auto .
rewrite /is_init /= => /> *.
smt().
auto .
smt().
qed .

lemma __round_ref1_proof _e _b_e _a _b_a _rc :
      (__round_ref1_spec _e _b_e _a _b_a _rc).
proof.
rewrite /__round_ref1_spec .
proc; auto.
while (0 <= y /\ y <= 5 /\
      ((1 <= y) => (BArray200.is_init b_e 0 (y*40)))).
auto .
ecall (__set_row_ref1_proof param_7 b_param param_6 (BArray40.init_arr
                                                    (JWord.W8.of_int 255)) 
       param_5 param_4).
auto .
ecall (__rol_sum_ref1_proof param_3 (BArray200.init_arr (JWord.W8.of_int 255)) 
       param_2 (BArray40.init_arr (JWord.W8.of_int 255)) param_1).
auto .
rewrite /is_init /= => /> *.
smt(BArray200.init_arrP BArray40.init_arrP).
auto.
ecall (__theta_rol_ref1_proof param_0 (BArray40.init_arr (JWord.W8.of_int 255))).
auto .
ecall (__theta_sum_ref1_proof param (BArray200.init_arr (JWord.W8.of_int 255))).
auto .
smt(BArray200.init_arrP BArray40.init_arrP).
qed .

lemma __keccakf1600_ref1_proof _a _b_a : (__keccakf1600_ref1_spec _a _b_a).
proof.
rewrite /__keccakf1600_ref1_spec .
proc; auto.
while (JWord.W64.(\ule) JWord.W64.zero c /\ JWord.W64.(\ule) c (JWord.W64.of_int 24)).
auto .
ecall (__round_ref1_proof param_4 (BArray200.init_arr (JWord.W8.of_int 255)) 
       param_3 (BArray200.init_arr (JWord.W8.of_int 255)) param_2).
auto .
ecall (__round_ref1_proof param_1 b_param param_0 (BArray200.init_arr
                                                  (JWord.W8.of_int 255)) param).
auto .
move => &hr.
rewrite /is_init /= => /> *.
progress.
smt(JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
smt(BArray200.init_arrP).
smt(JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
have help : JWord.W64.(\ult) c{hr} (JWord.W64.of_int 23) =>
JWord.W64.(+) c{hr} (JWord.W64.of_int 2) = JWord.W64.of_int((JWord.W64.to_uint c{hr}) + 2).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
rewrite help.
smt().
rewrite JWord.W64.ule_of_int.
smt().
auto .
smt(BArray200.init_arrP).
qed .

lemma _keccakf1600_ref1_proof _a _b_a : (_keccakf1600_ref1_spec _a _b_a).
proof.
rewrite /_keccakf1600_ref1_spec .
proc; auto .
ecall (__keccakf1600_ref1_proof param (BArray200.init_arr (JWord.W8.of_int 255))).
auto .
smt(BArray200.init_arrP).
qed .

lemma __keccak_init_ref1_proof _state _b_state :
      (__keccak_init_ref1_spec _state _b_state).
proof.
rewrite /__keccak_init_ref1_spec .
proc; auto .
while (0 <= i /\ i <= 25 /\
      ((1 <= i) => (BArray200.is_init b_state 0 (8 * i)))).
auto .
rewrite /is_init /= => /> *.
smt().
auto .
smt().
qed .

lemma __keccakf1600_pround_avx2_proof _state _b_state :
      (__keccakf1600_pround_avx2_spec _state _b_state).
      proof.
        proc.
      rewrite /=.
        wp -1.
        seq 1: (true).
        auto.
        sp 20.
        sp 10.
        sp 10.
        sp 20.
        sp 10.
        sp 10.
        sp 10.
        sp.
        conseq (_: true ==> _).
      skip.
      smt(BArray224.init_arrP).
qed .

lemma __keccakf1600_avx2_proof _state _b_state :
      (__keccakf1600_avx2_spec _state _b_state).
proof.
rewrite /__keccakf1600_avx2_spec .
proc; auto .
while (1 <= r /\ r <= 24).
auto .
ecall (__keccakf1600_pround_avx2_proof param (BArray224.init_arr
                                             (JWord.W8.of_int 255))).
auto .
smt(BArray224.init_arrP).
auto .
ecall (__keccakf1600_pround_avx2_proof param (BArray224.init_arr
                                             (JWord.W8.of_int 255))).
auto .
smt(BArray224.init_arrP).
qed .

lemma _keccakf1600_avx2_proof _state _b_state :
      (_keccakf1600_avx2_spec _state _b_state).
proof.
rewrite /_keccakf1600_avx2_spec .
proc; auto .
ecall (__keccakf1600_avx2_proof param (BArray224.init_arr (JWord.W8.of_int 255))).
auto .
smt(BArray224.init_arrP).
qed .

lemma __stavx2_pack_proof _st _b_st : (__stavx2_pack_spec _st _b_st).
proof.
rewrite /__stavx2_pack_spec .
proc; auto .
rewrite /is_init /= .
smt().
qed .

lemma __stavx2_unpack_proof _st _b_st _state _b_state :
      (__stavx2_unpack_spec _st _b_st _state _b_state).
proof.
rewrite /__stavx2_unpack_spec .
proc; auto .
rewrite /is_init /= .
smt().
qed .

lemma _keccakf1600_st25_avx2_proof _st25 _b_st25 :
      (_keccakf1600_st25_avx2_spec _st25 _b_st25).
proof.
rewrite /_keccakf1600_st25_avx2_spec .
proc; auto .
ecall (__stavx2_unpack_proof param_2 (BArray200.init_arr (JWord.W8.of_int 255)) 
       param_1 (BArray224.init_arr (JWord.W8.of_int 255))).
auto .
ecall (__keccakf1600_avx2_proof param_0 (BArray224.init_arr (JWord.W8.of_int 255))).
auto .
ecall (__stavx2_pack_proof param (BArray200.init_arr (JWord.W8.of_int 255))).
auto .
smt(BArray224.init_arrP BArray200.init_arrP).
qed .

lemma __m_ilen_read_upto8_at_proof _buf _lEN _tRAIL _cUR _aT :
      (__m_ilen_read_upto8_at_spec _buf _lEN _tRAIL _cUR _aT).
proof.
rewrite /__m_ilen_read_upto8_at_spec .
proc; auto .
if .
auto .
  if.
  if.
  wp.
skip.
smt().
  auto .
sp.
if .
auto .
ecall (__SHLQ_proof param_0 param).
  auto .
smt().
if .
if .
if .
  sp.
  inline __SHLQ.
  sp.
if.
  auto.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  sp.
  if.
  if.
  if.
  sp.
  if.
  if.
  sp.
  inline __SHLQ.
  auto.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  if.
  if.
  if.
  if.
  sp.
  if.
auto.
ecall (__SHLQ_proof param_6 param_5).
  auto .
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  if.
auto.
ecall (__SHLQ_proof param_8 param_7).
  auto .
  smt().
  skip.
  smt().
  skip.
  smt().
  exfalso.
  smt().
  exfalso.
smt().
qed.

lemma __m_ilen_read_upto16_at_proof _buf _lEN _tRAIL _cUR _aT :
    (__m_ilen_read_upto16_at_spec _buf _lEN _tRAIL _cUR _aT).
proof.
proc; auto .
if .
if.
if.
wp.
skip.
smt().
  auto .
sp.
if .
auto .
ecall (__SHLDQ_proof param_0 param).
  auto .
smt().
  if .
  sp.
wp.
  ecall (__m_ilen_read_upto8_at_proof param_5 param_4 param_3 param_2 param_1).
  skip.
  smt().
  auto.
  ecall (__m_ilen_read_upto8_at_proof param_15 param_14 param_13 param_12 param_11).
  auto.
  ecall (__m_ilen_read_upto8_at_proof param_10 param_9 param_8 param_7 param_6).
  auto.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
qed.

lemma __m_ilen_read_upto32_at_proof _buf _lEN _tRAIL _cUR _aT :
      (__m_ilen_read_upto32_at_spec _buf _lEN _tRAIL _cUR _aT).
proof.
rewrite /__m_ilen_read_upto32_at_spec .
proc; auto .
  if .
  if.
  if.
  auto .
  smt().
  sp.
  if.
auto.
smt().
if .
auto .
ecall (__m_ilen_read_upto16_at_proof param_3 param_2 param_1 param_0 param).
auto .
smt().
auto .
ecall (__m_ilen_read_upto16_at_proof param_13 param_12 param_11 param_10 
       param_9).
auto .
ecall (__m_ilen_read_upto16_at_proof param_8 param_7 param_6 param_5 param_4).
auto .
  smt().
  exfalso.
  smt().
  exfalso.
smt().
qed .

lemma __m_ilen_read_bcast_upto8_at_proof _buf _lEN _tRAIL _cUR _aT :
      (__m_ilen_read_bcast_upto8_at_spec _buf _lEN _tRAIL _cUR _aT).
proof.
rewrite /__m_ilen_read_bcast_upto8_at_spec .
proc; auto .
if .
  if.
  if.
auto.
smt().
  if .
auto.
ecall (__SHLQ_256_proof param_0 param).
auto .
smt().
auto.
ecall (__SHLQ_256_proof param_7 param_6).
auto .
ecall (__m_ilen_read_upto8_at_proof param_5 param_4 param_3 param_2 param_1).
auto .
exfalso.
smt().
exfalso.
smt().
qed .

lemma __m_ilen_write_upto8_proof _buf _lEN _w :
      (__m_ilen_write_upto8_spec _buf _lEN _w).
proof.
rewrite /__m_ilen_write_upto8_spec .
proc; auto .
smt().
qed .

lemma __m_ilen_write_upto16_proof _buf _lEN _w :
      (__m_ilen_write_upto16_spec _buf _lEN _w).
proof.
rewrite /__m_ilen_write_upto16_spec .
proc; auto .
if .
if .
if.
  if.
auto.
smt().
auto.
ecall (__m_ilen_write_upto8_proof param_1 param_0 param).
auto .
smt().
auto .
smt().
exfalso.
smt().
exfalso.
smt().
qed .

lemma __m_ilen_write_upto32_proof _buf _lEN _w :
      (__m_ilen_write_upto32_spec _buf _lEN _w).
proof.
rewrite /__m_ilen_write_upto32_spec .
proc; auto .
if .
if .
if.
if.
auto .
smt().
auto.
ecall (__m_ilen_write_upto16_proof param_1 param_0 param).
auto .
smt().
auto .
smt().
exfalso.
smt().
exfalso.
smt().
qed .

lemma __m_rlen_read_upto8_proof _buf _len :
      (__m_rlen_read_upto8_spec _buf _len).
      proof.
      admit.
qed .

lemma __m_rlen_write_upto8_proof _buf _data _len :
      (__m_rlen_write_upto8_spec _buf _data _len).
      proof.
      admit.
qed .

lemma __u64_to_u256_proof _x _l : (__u64_to_u256_spec _x _l).
proof.
rewrite /__u64_to_u256_spec .
proc; auto .
qed .

lemma __state_init_avx2_proof  : (__state_init_avx2_spec).
proof.
rewrite /__state_init_avx2_spec .
proc; auto .
while (0 <= i /\ i <= 7 /\
      ((1 <= i) => (BArray224.is_init b_st 0 (i * 32)))).
auto .
rewrite /is_init /= => /> *.
smt().
auto .
smt().
qed .

lemma __perm_reg3456_avx2_proof _r3 _r4 _r5 _r6 :
      (__perm_reg3456_avx2_spec _r3 _r4 _r5 _r6).
proof.
rewrite /__perm_reg3456_avx2_spec .
proc; auto .
qed .

lemma __unperm_reg3456_avx2_proof _st3 _st4 _st5 _st6 :
      (__unperm_reg3456_avx2_spec _st3 _st4 _st5 _st6).
proof.
rewrite /__unperm_reg3456_avx2_spec .
proc; auto .
qed .

lemma __addstate_r3456_avx2_proof _st _b_st _r3 _r4 _r5 _r6 :
      (__addstate_r3456_avx2_spec _st _b_st _r3 _r4 _r5 _r6).
proof.
rewrite /__addstate_r3456_avx2_spec .
proc; auto .
ecall (__perm_reg3456_avx2_proof param_2 param_1 param_0 param).
auto .
smt(BArray224.init_arrP).
qed .

lemma __stavx2_pos_avx2_proof _pOS : (__stavx2_pos_avx2_spec _pOS).
proof.
rewrite /__stavx2_pos_avx2_spec .
proc; auto .
qed .

lemma __addratebit_avx2_proof _st _b_st _rATE_8 :
      (__addratebit_avx2_spec _st _b_st _rATE_8).
proof.
rewrite /__addratebit_avx2_spec .
proc; auto .
if .
auto .
  rewrite /is_init /=.
  sp.
  seq 1 : (#pre /\ 0 <= result_0 /\ result_0 < 7).
ecall (__stavx2_pos_avx2_proof param).
  auto .
  if.
  sp.
  if.
  auto.
  smt(BArray224.init_arrP).
  auto.
ecall (__u64_to_u256_proof param_1 param_0).
  auto .
  smt(BArray224.init_arrP).
  exfalso.
  smt().
  exfalso.
smt().
qed .

lemma a_1____a_ilen_read_upto8_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_1____a_ilen_read_upto8_at_spec _buf _b_buf _offset _dELTA _lEN
      _tRAIL _cUR _aT).
proof.
rewrite /a_1____a_ilen_read_upto8_at_spec .
proc; auto .
if .
if.
  if.
  auto.
  smt().
  auto.
  sp.
  if.
  auto.
ecall (__SHLQ_proof param_0 param).
  auto .
  smt().
  if.
  if.
  if.
  if.
  if.
  sp.
seq 1 : (#pre).
  ecall (__SHLQ_proof param_2 param_1).
  auto.
  sp.
  if.
  if.
  if.
  if.
  if.
  sp.
seq 1 : (#pre).
  ecall (__SHLQ_proof param_4 param_3).
  auto.
  sp.
  if.
  if.
  if.
  if.
  if.
  if.
auto.
ecall (__SHLQ_proof param_6 param_5).
auto.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  sp.
  if.
  if.
  if.
  if.
  if.
sp.
seq 1 : (#pre).
  ecall (__SHLQ_proof param_4 param_3).
  auto.
  sp.
  if.
  if.
  if.
  if.
  if.
  if.
  auto.
  ecall (__SHLQ_proof param_6 param_5).
  auto.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  if.
  if.
  if.
  if.
  if.
  if.
  auto.
ecall (__SHLQ_proof param_6 param_5).
  auto .
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  if.
  auto.
  ecall (__SHLQ_proof param_8 param_7).
  auto.
  smt().
  skip.
  smt().
  skip.
  smt().
  exfalso.
  smt().
  exfalso.
smt().
qed .

lemma a_1____a_ilen_read_upto16_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_1____a_ilen_read_upto16_at_spec _buf _b_buf _offset _dELTA _lEN
      _tRAIL _cUR _aT).
proof.
rewrite /a_1____a_ilen_read_upto16_at_spec .
  proc; auto .
sp.
  if .
  if.
  if.
auto .
smt().
sp.
  if .
  if.
  if.
  if.
  if.
auto .
ecall (__SHLDQ_proof param_0 param).
auto .
smt().
  auto .
  ecall (__SHLDQ_proof param_0 param).
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  exfalso.
  smt().
  if.
auto.
ecall (a_1____a_ilen_read_upto8_at_proof param_7 b_param param_6 param_5 
       param_4 param_3 param_2 param_1).
auto .
smt().
auto .
ecall (a_1____a_ilen_read_upto8_at_proof param_21 b_param_0 param_20 
       param_19 param_18 param_17 param_16 param_15).
auto .
ecall (a_1____a_ilen_read_upto8_at_proof param_14 b_param_1 param_13 
       param_12 param_11 param_10 param_9 param_8).
auto .
  smt().
  exfalso.
  smt().
  exfalso.
smt().
qed .

lemma a_1____a_ilen_read_upto32_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_1____a_ilen_read_upto32_at_spec _buf _b_buf _offset _dELTA _lEN
      _tRAIL _cUR _aT).
proof.
      admit.
qed .

lemma a_1____a_ilen_read_bcast_upto8_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_1____a_ilen_read_bcast_upto8_at_spec _buf _b_buf _offset _dELTA 
      _lEN _tRAIL _cUR _aT).
proof.
      admit.
qed .

lemma a_1____a_ilen_write_upto8_proof _buf _b_buf _offset _dELTA _lEN _w :
      (a_1____a_ilen_write_upto8_spec _buf _b_buf _offset _dELTA _lEN _w).
proof.
rewrite /a_1____a_ilen_write_upto8_spec .
proc; auto .
rewrite /is_init /valid /= .
smt().
qed .

lemma a_1____a_ilen_write_upto16_proof _buf _b_buf _offset _dELTA _lEN _w :
      (a_1____a_ilen_write_upto16_spec _buf _b_buf _offset _dELTA _lEN _w).
proof.
admit.
qed .

lemma a_1____a_ilen_write_upto32_proof _buf _b_buf _offset _dELTA _lEN _w :
      (a_1____a_ilen_write_upto32_spec _buf _b_buf _offset _dELTA _lEN _w).
proof.
admit.
qed .

lemma a_1____a_rlen_read_upto8_proof _a _b_a _off _len :
      (a_1____a_rlen_read_upto8_spec _a _b_a _off _len).
proof.
admit.
qed .

lemma a_1____a_rlen_read_upto8_noninline_proof _a _b_a _off_ _len_ :
      (a_1____a_rlen_read_upto8_noninline_spec _a _b_a _off_ _len_).
proof.
admit.
qed .

lemma a_1____a_rlen_write_upto8_proof _buf _b_buf _off _data _len :
      (a_1____a_rlen_write_upto8_spec _buf _b_buf _off _data _len).
proof.
admit.
qed .

lemma a_1____addstate_avx2_proof _st _b_st _aT _buf _b_buf _offset __LEN __TRAILB :
      (a_1____addstate_avx2_spec _st _b_st _aT _buf _b_buf _offset __LEN
      __TRAILB).
proof.
admit.
qed .

lemma a_1____absorb_avx2_proof _st _b_st _aT _buf _b_buf __TRAILB __RATE8 :
      (a_1____absorb_avx2_spec _st _b_st _aT _buf _b_buf __TRAILB __RATE8).
proof.
admit.
qed .

lemma a_1____dumpstate_avx2_proof _buf _b_buf _offset __LEN _st _b_st :
      (a_1____dumpstate_avx2_spec _buf _b_buf _offset __LEN _st _b_st).
proof.
admit.
qed .

lemma a_1____squeeze_avx2_proof _st _b_st _buf _b_buf __RATE8 :
      (a_1____squeeze_avx2_spec _st _b_st _buf _b_buf __RATE8).
proof.
admit.
qed .

lemma a_2____a_ilen_read_upto8_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_2____a_ilen_read_upto8_at_spec _buf _b_buf _offset _dELTA _lEN
      _tRAIL _cUR _aT).
proof.
admit.
qed .

lemma a_2____a_ilen_read_upto16_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_2____a_ilen_read_upto16_at_spec _buf _b_buf _offset _dELTA _lEN
      _tRAIL _cUR _aT).
proof.
admit.
qed .

lemma a_2____a_ilen_read_upto32_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_2____a_ilen_read_upto32_at_spec _buf _b_buf _offset _dELTA _lEN
      _tRAIL _cUR _aT).
proof.
admit.
qed .

lemma a_2____a_ilen_read_bcast_upto8_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_2____a_ilen_read_bcast_upto8_at_spec _buf _b_buf _offset _dELTA 
      _lEN _tRAIL _cUR _aT).
proof.
admit.
qed .

lemma a_2____a_ilen_write_upto8_proof _buf _b_buf _offset _dELTA _lEN _w :
      (a_2____a_ilen_write_upto8_spec _buf _b_buf _offset _dELTA _lEN _w).
proof.
rewrite /a_2____a_ilen_write_upto8_spec .
proc; auto .
rewrite /is_init /= .
smt().
qed .

lemma a_2____a_ilen_write_upto16_proof _buf _b_buf _offset _dELTA _lEN _w :
      (a_2____a_ilen_write_upto16_spec _buf _b_buf _offset _dELTA _lEN _w).
proof.
admit.
qed .

lemma a_2____a_ilen_write_upto32_proof _buf _b_buf _offset _dELTA _lEN _w :
      (a_2____a_ilen_write_upto32_spec _buf _b_buf _offset _dELTA _lEN _w).
proof.
admit.
qed .

lemma a_2____a_rlen_read_upto8_proof _a _b_a _off _len :
      (a_2____a_rlen_read_upto8_spec _a _b_a _off _len).
proof.
admit.
qed .

lemma a_2____a_rlen_read_upto8_noninline_proof _a _b_a _off_ _len_ :
      (a_2____a_rlen_read_upto8_noninline_spec _a _b_a _off_ _len_).
proof.
admit.
qed .

lemma a_2____a_rlen_write_upto8_proof _buf _b_buf _off _data _len :
      (a_2____a_rlen_write_upto8_spec _buf _b_buf _off _data _len).
proof.
admit.
qed .

lemma a_2____addstate_avx2_proof _st _b_st _aT _buf _b_buf _offset __LEN __TRAILB :
      (a_2____addstate_avx2_spec _st _b_st _aT _buf _b_buf _offset __LEN
      __TRAILB).
proof.
admit.
qed .

lemma a_2____absorb_avx2_proof _st _b_st _aT _buf _b_buf __TRAILB __RATE8 :
      (a_2____absorb_avx2_spec _st _b_st _aT _buf _b_buf __TRAILB __RATE8).
proof.
admit.
qed .

lemma a_2____dumpstate_avx2_proof _buf _b_buf _offset __LEN _st _b_st :
      (a_2____dumpstate_avx2_spec _buf _b_buf _offset __LEN _st _b_st).
proof.
admit.
qed .

lemma a_2____squeeze_avx2_proof _st _b_st _buf _b_buf __RATE8 :
      (a_2____squeeze_avx2_spec _st _b_st _buf _b_buf __RATE8).
proof.
admit.
qed.

lemma a_32____a_ilen_read_upto8_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_32____a_ilen_read_upto8_at_spec _buf _b_buf _offset _dELTA _lEN
      _tRAIL _cUR _aT).
proof.
admit.
qed .

lemma a_32____a_ilen_read_upto16_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_32____a_ilen_read_upto16_at_spec _buf _b_buf _offset _dELTA 
      _lEN _tRAIL _cUR _aT).
proof.
admit.
qed .

lemma a_32____a_ilen_read_upto32_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_32____a_ilen_read_upto32_at_spec _buf _b_buf _offset _dELTA 
      _lEN _tRAIL _cUR _aT).
proof.
admit.
qed .

lemma a_32____a_ilen_read_bcast_upto8_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_32____a_ilen_read_bcast_upto8_at_spec _buf _b_buf _offset _dELTA
      _lEN _tRAIL _cUR _aT).
proof.
admit.
qed .

lemma a_32____a_ilen_write_upto8_proof _buf _b_buf _offset _dELTA _lEN _w :
      (a_32____a_ilen_write_upto8_spec _buf _b_buf _offset _dELTA _lEN _w).
proof.
rewrite /a_32____a_ilen_write_upto8_spec .
proc; auto .
rewrite /is_init /valid /= .
smt().
qed .

lemma a_32____a_ilen_write_upto16_proof _buf _b_buf _offset _dELTA _lEN _w :
      (a_32____a_ilen_write_upto16_spec _buf _b_buf _offset _dELTA _lEN _w).
proof.
admit.
qed .

lemma a_32____a_ilen_write_upto32_proof _buf _b_buf _offset _dELTA _lEN _w :
      (a_32____a_ilen_write_upto32_spec _buf _b_buf _offset _dELTA _lEN _w).
proof.
admit.
qed .

lemma a_32____a_rlen_read_upto8_proof _a _b_a _off _len :
      (a_32____a_rlen_read_upto8_spec _a _b_a _off _len).
proof.
admit.
qed .

lemma a_32____a_rlen_read_upto8_noninline_proof _a _b_a _off_ _len_ :
      (a_32____a_rlen_read_upto8_noninline_spec _a _b_a _off_ _len_).
proof.
admit.
qed .

lemma a_32____a_rlen_write_upto8_proof _buf _b_buf _off _data _len :
      (a_32____a_rlen_write_upto8_spec _buf _b_buf _off _data _len).
proof.
admit.
qed .

lemma a_32____addstate_avx2_proof _st _b_st _aT _buf _b_buf _offset __LEN __TRAILB :
      (a_32____addstate_avx2_spec _st _b_st _aT _buf _b_buf _offset __LEN
      __TRAILB).
proof.
admit.
qed .

lemma a_32____absorb_avx2_proof _st _b_st _aT _buf _b_buf __TRAILB __RATE8 :
      (a_32____absorb_avx2_spec _st _b_st _aT _buf _b_buf __TRAILB __RATE8).
proof.
admit.
qed .

lemma a_32____dumpstate_avx2_proof _buf _b_buf _offset __LEN _st _b_st :
      (a_32____dumpstate_avx2_spec _buf _b_buf _offset __LEN _st _b_st).
proof.
admit.
qed .

lemma a_32____squeeze_avx2_proof _st _b_st _buf _b_buf __RATE8 :
      (a_32____squeeze_avx2_spec _st _b_st _buf _b_buf __RATE8).
proof.
admit.
qed .

lemma a_N____a_ilen_read_upto8_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_N____a_ilen_read_upto8_at_spec _buf _b_buf _offset _dELTA _lEN
      _tRAIL _cUR _aT).
proof.
admit.
qed .

lemma a_N____a_ilen_read_upto16_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_N____a_ilen_read_upto16_at_spec _buf _b_buf _offset _dELTA _lEN
      _tRAIL _cUR _aT).
proof.
admit.
qed .

lemma a_N____a_ilen_read_upto32_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_N____a_ilen_read_upto32_at_spec _buf _b_buf _offset _dELTA _lEN
      _tRAIL _cUR _aT).
proof.
admit.
qed .

lemma a_N____a_ilen_read_bcast_upto8_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_N____a_ilen_read_bcast_upto8_at_spec _buf _b_buf _offset _dELTA 
      _lEN _tRAIL _cUR _aT).
proof.
admit.
qed .

lemma a_N____a_ilen_write_upto8_proof _buf _b_buf _offset _dELTA _lEN _w :
      (a_N____a_ilen_write_upto8_spec _buf _b_buf _offset _dELTA _lEN _w).
proof.
rewrite /a_N____a_ilen_write_upto8_spec .
proc; auto .
rewrite /is_init /valid /= .
smt().
qed .

lemma a_N____a_ilen_write_upto16_proof _buf _b_buf _offset _dELTA _lEN _w :
      (a_N____a_ilen_write_upto16_spec _buf _b_buf _offset _dELTA _lEN _w).
proof.
admit.
qed .

lemma a_N____a_ilen_write_upto32_proof _buf _b_buf _offset _dELTA _lEN _w :
      (a_N____a_ilen_write_upto32_spec _buf _b_buf _offset _dELTA _lEN _w).
proof.
admit.
qed .

lemma a_N____a_rlen_read_upto8_proof _a _b_a _off _len :
      (a_N____a_rlen_read_upto8_spec _a _b_a _off _len).
proof.
admit.
qed .

lemma a_N____a_rlen_read_upto8_noninline_proof _a _b_a _off_ _len_ :
      (a_N____a_rlen_read_upto8_noninline_spec _a _b_a _off_ _len_).
proof.
admit.
qed .

lemma a_N____a_rlen_write_upto8_proof _buf _b_buf _off _data _len :
      (a_N____a_rlen_write_upto8_spec _buf _b_buf _off _data _len).
proof.
admit.
qed .

lemma a_N____addstate_avx2_proof _st _b_st _aT _buf _b_buf _offset __LEN __TRAILB :
      (a_N____addstate_avx2_spec _st _b_st _aT _buf _b_buf _offset __LEN
      __TRAILB).
proof.
admit.
qed .

lemma a_N____absorb_avx2_proof _st _b_st _aT _buf _b_buf __TRAILB __RATE8 :
      (a_N____absorb_avx2_spec _st _b_st _aT _buf _b_buf __TRAILB __RATE8).
proof.
admit.
qed .

lemma a_N____dumpstate_avx2_proof _buf _b_buf _offset __LEN _st _b_st :
      (a_N____dumpstate_avx2_spec _buf _b_buf _offset __LEN _st _b_st).
proof.
admit.
qed .

lemma a_N____squeeze_avx2_proof _st _b_st _buf _b_buf __RATE8 :
      (a_N____squeeze_avx2_spec _st _b_st _buf _b_buf __RATE8).
proof.
admit.
qed .

lemma a_M____a_ilen_read_upto8_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_M____a_ilen_read_upto8_at_spec _buf _b_buf _offset _dELTA _lEN
      _tRAIL _cUR _aT).
proof.
admit.
qed .

lemma a_M____a_ilen_read_upto16_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_M____a_ilen_read_upto16_at_spec _buf _b_buf _offset _dELTA _lEN
      _tRAIL _cUR _aT).
proof.
admit.
qed .

lemma a_M____a_ilen_read_upto32_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_M____a_ilen_read_upto32_at_spec _buf _b_buf _offset _dELTA _lEN
      _tRAIL _cUR _aT).
proof.
admit.
qed .

lemma a_M____a_ilen_read_bcast_upto8_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_M____a_ilen_read_bcast_upto8_at_spec _buf _b_buf _offset _dELTA 
      _lEN _tRAIL _cUR _aT).
proof.
admit.
qed .

lemma a_M____a_ilen_write_upto8_proof _buf _b_buf _offset _dELTA _lEN _w :
      (a_M____a_ilen_write_upto8_spec _buf _b_buf _offset _dELTA _lEN _w).
proof.
rewrite /a_M____a_ilen_write_upto8_spec .
proc; auto .
rewrite /is_init /valid /= .
smt().
qed .

lemma a_M____a_ilen_write_upto16_proof _buf _b_buf _offset _dELTA _lEN _w :
      (a_M____a_ilen_write_upto16_spec _buf _b_buf _offset _dELTA _lEN _w).
proof.
admit.
qed .

lemma a_M____a_ilen_write_upto32_proof _buf _b_buf _offset _dELTA _lEN _w :
      (a_M____a_ilen_write_upto32_spec _buf _b_buf _offset _dELTA _lEN _w).
proof.
admit.
qed .

lemma a_M____a_rlen_read_upto8_proof _a _b_a _off _len :
      (a_M____a_rlen_read_upto8_spec _a _b_a _off _len).
proof.
admit.
qed .

lemma a_M____a_rlen_read_upto8_noninline_proof _a _b_a _off_ _len_ :
      (a_M____a_rlen_read_upto8_noninline_spec _a _b_a _off_ _len_).
proof.
admit.
qed .

lemma a_M____a_rlen_write_upto8_proof _buf _b_buf _off _data _len :
      (a_M____a_rlen_write_upto8_spec _buf _b_buf _off _data _len).
proof.
admit.
qed .

lemma a_M____addstate_avx2_proof _st _b_st _aT _buf _b_buf _offset __LEN __TRAILB :
      (a_M____addstate_avx2_spec _st _b_st _aT _buf _b_buf _offset __LEN
      __TRAILB).
proof.
admit.
qed .

lemma a_M____absorb_avx2_proof _st _b_st _aT _buf _b_buf __TRAILB __RATE8 :
      (a_M____absorb_avx2_spec _st _b_st _aT _buf _b_buf __TRAILB __RATE8).
proof.
admit.
qed .

lemma a_M____dumpstate_avx2_proof _buf _b_buf _offset __LEN _st _b_st :
      (a_M____dumpstate_avx2_spec _buf _b_buf _offset __LEN _st _b_st).
proof.
admit.
qed .

lemma a_M____squeeze_avx2_proof _st _b_st _buf _b_buf __RATE8 :
      (a_M____squeeze_avx2_spec _st _b_st _buf _b_buf __RATE8).
proof.
admit.
qed .

lemma a_LENN____a_ilen_read_upto8_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_LENN____a_ilen_read_upto8_at_spec _buf _b_buf _offset _dELTA 
      _lEN _tRAIL _cUR _aT).
proof.
admit.
qed .

lemma a_LENN____a_ilen_read_upto16_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_LENN____a_ilen_read_upto16_at_spec _buf _b_buf _offset _dELTA 
      _lEN _tRAIL _cUR _aT).
proof.
admit.
qed .

lemma a_LENN____a_ilen_read_upto32_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_LENN____a_ilen_read_upto32_at_spec _buf _b_buf _offset _dELTA 
      _lEN _tRAIL _cUR _aT).
proof.
admit.
qed .

lemma a_LENN____a_ilen_read_bcast_upto8_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_LENN____a_ilen_read_bcast_upto8_at_spec _buf _b_buf _offset 
      _dELTA _lEN _tRAIL _cUR _aT).
proof.
admit.
qed .

lemma a_LENN____a_ilen_write_upto8_proof _buf _b_buf _offset _dELTA _lEN _w :
      (a_LENN____a_ilen_write_upto8_spec _buf _b_buf _offset _dELTA _lEN _w).
proof.
admit.
qed .

lemma a_LENN____a_ilen_write_upto16_proof _buf _b_buf _offset _dELTA _lEN _w :
      (a_LENN____a_ilen_write_upto16_spec _buf _b_buf _offset _dELTA _lEN _w).
proof.
admit.
qed.

lemma a_LENN____a_ilen_write_upto32_proof _buf _b_buf _offset _dELTA _lEN _w :
      (a_LENN____a_ilen_write_upto32_spec _buf _b_buf _offset _dELTA _lEN _w).
proof.
admit.
qed .

lemma a_LENN____a_rlen_read_upto8_proof _a _b_a _off _len :
      (a_LENN____a_rlen_read_upto8_spec _a _b_a _off _len).
proof.
admit.
qed .

lemma a_LENN____a_rlen_read_upto8_noninline_proof _a _b_a _off_ _len_ :
      (a_LENN____a_rlen_read_upto8_noninline_spec _a _b_a _off_ _len_).
proof.
admit.
qed .

lemma a_LENN____a_rlen_write_upto8_proof _buf _b_buf _off _data _len :
      (a_LENN____a_rlen_write_upto8_spec _buf _b_buf _off _data _len).
proof.
admit.
qed .

lemma a_LENN____addstate_avx2_proof _st _b_st _aT _buf _b_buf _offset __LEN __TRAILB :
      (a_LENN____addstate_avx2_spec _st _b_st _aT _buf _b_buf _offset 
      __LEN __TRAILB).
proof.
admit.
qed .

lemma a_LENN____absorb_avx2_proof _st _b_st _aT _buf _b_buf __TRAILB __RATE8 :
      (a_LENN____absorb_avx2_spec _st _b_st _aT _buf _b_buf __TRAILB __RATE8).
proof.
admit.
qed .

lemma a_LENN____dumpstate_avx2_proof _buf _b_buf _offset __LEN _st _b_st :
      (a_LENN____dumpstate_avx2_spec _buf _b_buf _offset __LEN _st _b_st).
proof.
admit.
qed .

lemma a_LENN____squeeze_avx2_proof _st _b_st _buf _b_buf __RATE8 :
      (a_LENN____squeeze_avx2_spec _st _b_st _buf _b_buf __RATE8).
proof.
admit.
qed .

lemma a_KN____a_ilen_read_upto8_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_KN____a_ilen_read_upto8_at_spec _buf _b_buf _offset _dELTA _lEN
      _tRAIL _cUR _aT).
proof.
admit.
qed .

lemma a_KN____a_ilen_read_upto16_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_KN____a_ilen_read_upto16_at_spec _buf _b_buf _offset _dELTA 
      _lEN _tRAIL _cUR _aT).
proof.
admit.
qed .

lemma a_KN____a_ilen_read_upto32_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_KN____a_ilen_read_upto32_at_spec _buf _b_buf _offset _dELTA 
      _lEN _tRAIL _cUR _aT).
proof.
admit.
qed .

lemma a_KN____a_ilen_read_bcast_upto8_at_proof _buf _b_buf _offset _dELTA _lEN _tRAIL _cUR _aT :
      (a_KN____a_ilen_read_bcast_upto8_at_spec _buf _b_buf _offset _dELTA
      _lEN _tRAIL _cUR _aT).
proof.
admit.
qed .

lemma a_KN____a_ilen_write_upto8_proof _buf _b_buf _offset _dELTA _lEN _w :
      (a_KN____a_ilen_write_upto8_spec _buf _b_buf _offset _dELTA _lEN _w).
proof.
rewrite /a_KN____a_ilen_write_upto8_spec .
  proc; auto .
rewrite /is_init /= .
smt().
qed .

lemma a_KN____a_ilen_write_upto16_proof _buf _b_buf _offset _dELTA _lEN _w :
      (a_KN____a_ilen_write_upto16_spec _buf _b_buf _offset _dELTA _lEN _w).
proof.
admit.
qed .

lemma a_KN____a_ilen_write_upto32_proof _buf _b_buf _offset _dELTA _lEN _w :
      (a_KN____a_ilen_write_upto32_spec _buf _b_buf _offset _dELTA _lEN _w).
proof.
admit.
qed .

lemma a_KN____a_rlen_read_upto8_proof _a _b_a _off _len :
      (a_KN____a_rlen_read_upto8_spec _a _b_a _off _len).
proof.
admit.
qed .

lemma a_KN____a_rlen_read_upto8_noninline_proof _a _b_a _off_ _len_ :
      (a_KN____a_rlen_read_upto8_noninline_spec _a _b_a _off_ _len_).
proof.
admit.
qed .

lemma a_KN____a_rlen_write_upto8_proof _buf _b_buf _off _data _len :
      (a_KN____a_rlen_write_upto8_spec _buf _b_buf _off _data _len).
proof.
admit.
qed .

lemma a_KN____addstate_avx2_proof _st _b_st _aT _buf _b_buf _offset __LEN __TRAILB :
      (a_KN____addstate_avx2_spec _st _b_st _aT _buf _b_buf _offset __LEN
      __TRAILB).
proof.
admit.
qed .

lemma a_KN____absorb_avx2_proof _st _b_st _aT _buf _b_buf __TRAILB __RATE8 :
      (a_KN____absorb_avx2_spec _st _b_st _aT _buf _b_buf __TRAILB __RATE8).
proof.
admit.
qed .

lemma a_KN____dumpstate_avx2_proof _buf _b_buf _offset __LEN _st _b_st :
      (a_KN____dumpstate_avx2_spec _buf _b_buf _offset __LEN _st _b_st).
proof.
admit.
qed .

lemma a_KN____squeeze_avx2_proof _st _b_st _buf _b_buf __RATE8 :
      (a_KN____squeeze_avx2_spec _st _b_st _buf _b_buf __RATE8).
proof.
admit.
qed .

lemma __shake256_consider_permute_proof _state _b_state _offset :
      (__shake256_consider_permute_spec _state _b_state _offset).
proof.
rewrite /__shake256_consider_permute_spec .
proc; auto .
sp.
if .
if.
auto .
ecall (_keccakf1600_ref1_proof param (BArray200.init_arr (JWord.W8.of_int 255))).
auto .
smt(BArray200.init_arrP).
auto .
smt(BArray200.init_arrP).
exfalso.
smt().
qed .

lemma h_msg_proof _out _b_out _r _b_r _pkseed _b_pkseed _pkroot _b_pkroot _ctx_ptr _ctx_len _msg_ptr _msg_len :
      (h_msg_spec _out _b_out _r _b_r _pkseed _b_pkseed _pkroot _b_pkroot
      _ctx_ptr _ctx_len _msg_ptr _msg_len).
proof.
rewrite /h_msg_spec .
  proc; auto .
while ((0 <= i /\ i <= 49 /\
      ((1 <= i) => (BArray39.is_init b_out 0 i)))).
auto .
rewrite /is_init /=.
smt().
auto .
ecall (_keccakf1600_ref1_proof param_6 (BArray200.init_arr((JWord.W8.of_int 255)))).
auto .
ecall (__shake256_consider_permute_proof param_5 (BArray200.init_arr (JWord.W8.of_int 255)) param_4).
auto .
ecall (__shake256_consider_permute_proof param_3 (BArray200.init_arr (JWord.W8.of_int 255)) param_2).
        auto .
while (JWord.W64.(\ule) JWord.W64.zero msg_offset /\ JWord.W64.(\ule) msg_offset msg_len /\
       JMemory.is_valid 18446744073709551616 JMemory.Glob.mem_v
      (JWord.W64.to_uint _msg_ptr) (JWord.W64.to_uint _msg_len) /\
       msg_len = _msg_len /\ msg_ptr = _msg_ptr).
if .
auto .
ecall (_keccakf1600_ref1_proof param_1 (BArray200.init_arr (JWord.W8.of_int 255))).
auto .
rewrite /is_init /=.
rewrite /is_valid.
progress.
smt(BArray200.init_arrP).
have resolve_addition : (JWord.W64.of_int(i0) =
                         JWord.W64.of_int
                        (JWord.W64.to_uint msg_ptr{hr} + JWord.W64.to_uint msg_offset{hr})).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
have wrap_to_uint : (JWord.W64.to_uint(JWord.W64.of_int i0) =
                     JWord.W64.to_uint(JWord.W64.of_int
                    (JWord.W64.to_uint msg_ptr{hr} + JWord.W64.to_uint msg_offset{hr}))).
smt().
have unwrap : (i0 = (JWord.W64.to_uint msg_ptr{hr} + JWord.W64.to_uint msg_offset{hr})).
move: wrap_to_uint.
rewrite JWord.W64.of_uintK.
                      rewrite JWord.W64.of_uintK.
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
smt(JWord.W64.to_uint_cmp).
smt(JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
                      auto.
                      progress.
have resolve_addition : (JWord.W64.of_int(i0) =
                         JWord.W64.of_int
                        (JWord.W64.to_uint msg_ptr{hr} + JWord.W64.to_uint msg_offset{hr})).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
have wrap_to_uint : (JWord.W64.to_uint(JWord.W64.of_int i0) =
                     JWord.W64.to_uint(JWord.W64.of_int
                    (JWord.W64.to_uint msg_ptr{hr} + JWord.W64.to_uint msg_offset{hr}))).
smt().
have unwrap : (i0 = (JWord.W64.to_uint msg_ptr{hr} + JWord.W64.to_uint msg_offset{hr})).
move: wrap_to_uint.
rewrite JWord.W64.of_uintK.
rewrite JWord.W64.of_uintK.
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).


                
                      smt(JWord.W64.to_uint_cmp).
                      smt(JWord.W64.to_uint_cmp).
                      smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
                      smt(JWord.W64.to_uint_cmp).
                      smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
                      smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
                smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
auto.
while ((JWord.W64.(\ule) JWord.W64.zero ctx_offset) /\ (JWord.W64.(\ule) ctx_offset ctx_len) /\
       JMemory.is_valid 18446744073709551616 JMemory.Glob.mem_v
      (JWord.W64.to_uint _ctx_ptr) (JWord.W64.to_uint _ctx_len) /\
       ctx_len = _ctx_len /\ ctx_ptr = _ctx_ptr).
if .
auto .
ecall (_keccakf1600_ref1_proof param_0 (BArray200.init_arr (JWord.W8.of_int 255))).
auto .
rewrite /is_init /=.
rewrite /is_valid.
progress.
smt(BArray200.init_arrP).
have resolve_addition : (JWord.W64.of_int(i0) =
                         JWord.W64.of_int
                        (JWord.W64.to_uint ctx_ptr{hr} + JWord.W64.to_uint ctx_offset{hr})).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
have wrap_to_uint : (JWord.W64.to_uint(JWord.W64.of_int i0) =
                     JWord.W64.to_uint(JWord.W64.of_int
                    (JWord.W64.to_uint ctx_ptr{hr} + JWord.W64.to_uint ctx_offset{hr}))).
smt().
have unwrap : (i0 = (JWord.W64.to_uint ctx_ptr{hr} + JWord.W64.to_uint ctx_offset{hr})).
move: wrap_to_uint.
rewrite JWord.W64.of_uintK.
rewrite JWord.W64.of_uintK.
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
smt(JWord.W64.to_uint_cmp).
smt(JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
                      auto.
                      progress.
                have resolve_addition : (JWord.W64.of_int(i0) =
                         JWord.W64.of_int
                        (JWord.W64.to_uint ctx_ptr{hr} + JWord.W64.to_uint ctx_offset{hr})).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
have wrap_to_uint : (JWord.W64.to_uint(JWord.W64.of_int i0) =
                     JWord.W64.to_uint(JWord.W64.of_int
                    (JWord.W64.to_uint ctx_ptr{hr} + JWord.W64.to_uint ctx_offset{hr}))).
smt().
have unwrap : (i0 = (JWord.W64.to_uint ctx_ptr{hr} + JWord.W64.to_uint ctx_offset{hr})).
move: wrap_to_uint.
rewrite JWord.W64.of_uintK.
rewrite JWord.W64.of_uintK.
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
                      smt(JWord.W64.to_uint_cmp).
                      smt(JWord.W64.to_uint_cmp).
                      smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
                      smt(JWord.W64.to_uint_cmp).
                      smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
                      smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
                smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
                      auto .
                      while (0 <= i <= 24).
  auto => /> /#.
auto.
while (0 <= i <= 24).
  auto => /> /#.
auto.
while (0 <= i <= 24).
  auto => /> /#.
auto.
ecall (__keccak_init_ref1_proof param b_param).
                      auto .
                
                      smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp BArray200.init_arrP).
qed .

lemma __H_msg_proof _out _b_out _r _b_r _pkseed _b_pkseed _pkroot _b_pkroot _ctx_ptr _ctx_len _msg_ptr _msg_len :
      (__H_msg_spec _out _b_out _r _b_r _pkseed _b_pkseed _pkroot _b_pkroot
      _ctx_ptr _ctx_len _msg_ptr _msg_len).
proof.
rewrite /__H_msg_spec .
proc; auto .
ecall (h_msg_proof param_6 b_param param_5 (BArray24.init_arr (JWord.W8.of_int 255)
                                           ) param_4 (BArray24.init_arr
                                                     (JWord.W8.of_int 255)) 
       param_3 (BArray24.init_arr (JWord.W8.of_int 255)) param_2 param_1 param_0 
       param).
auto .
smt(BArray39.init_arrP BArray32.init_arrP BArray24.init_arrP).
qed .

lemma pRF_msg_proof _out _b_out _skprf _b_skprf _optrand _b_optrand _ctx_ptr _ctx_len _msg_ptr _msg_len :
      (pRF_msg_spec _out _b_out _skprf _b_skprf _optrand _b_optrand _ctx_ptr
      _ctx_len _msg_ptr _msg_len).
proof.
rewrite /pRF_msg_spec .
proc; auto .
while (0 <= i <= 24 /\ BArray24.is_init b_out 0 i).
  auto => /> &hr h0 h1 hb hi.
  split; 1: smt(). move=> _.
  split; 1: smt(). move=> _.
  split; 1: smt().
  by apply BArray24.is_init_set_last.
auto.
ecall (_keccakf1600_ref1_proof param_6 (BArray200.init_arr (JWord.W8.of_int 255))).
auto .
ecall (__shake256_consider_permute_proof param_5 (BArray200.init_arr(JWord.W8.of_int 255)) param_4).
auto .
ecall (__shake256_consider_permute_proof param_3 (BArray200.init_arr
                                                 (JWord.W8.of_int 255)) param_2).
auto .
while ((JWord.W64.(\ule) JWord.W64.zero msg_offset) /\ (JWord.W64.(\ule) msg_offset msg_len) /\
       (JMemory.is_valid 18446744073709551616 JMemory.Glob.mem_v
       (JWord.W64.to_uint _msg_ptr) (JWord.W64.to_uint _msg_len)) /\
        msg_ptr = _msg_ptr /\ msg_len = _msg_len).
auto .
if .
auto .
ecall (_keccakf1600_ref1_proof param_1 (BArray200.init_arr (JWord.W8.of_int 255))).
auto .
rewrite /is_init /=.
rewrite /is_valid.
progress.
smt(BArray200.init_arrP).
have resolve_addition : (JWord.W64.of_int(i0) =
                         JWord.W64.of_int
                        (JWord.W64.to_uint msg_ptr{hr} + JWord.W64.to_uint msg_offset{hr})).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
have wrap_to_uint : (JWord.W64.to_uint(JWord.W64.of_int i0) =
                     JWord.W64.to_uint(JWord.W64.of_int
                    (JWord.W64.to_uint msg_ptr{hr} + JWord.W64.to_uint msg_offset{hr}))).
smt().
have unwrap : (i0 = (JWord.W64.to_uint msg_ptr{hr} + JWord.W64.to_uint msg_offset{hr})).
move: wrap_to_uint.
rewrite JWord.W64.of_uintK.
rewrite JWord.W64.of_uintK.
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
smt(JWord.W64.to_uint_cmp).
smt(JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
                      auto .
rewrite /is_valid.
progress.
have resolve_addition : (JWord.W64.of_int(i0) =
                         JWord.W64.of_int
                        (JWord.W64.to_uint msg_ptr{hr} + JWord.W64.to_uint msg_offset{hr})).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
have wrap_to_uint : (JWord.W64.to_uint(JWord.W64.of_int i0) =
                     JWord.W64.to_uint(JWord.W64.of_int
                    (JWord.W64.to_uint msg_ptr{hr} + JWord.W64.to_uint msg_offset{hr}))).
smt().
have unwrap : (i0 = (JWord.W64.to_uint msg_ptr{hr} + JWord.W64.to_uint msg_offset{hr})).
move: wrap_to_uint.
rewrite JWord.W64.of_uintK.
rewrite JWord.W64.of_uintK.
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
smt(JWord.W64.to_uint_cmp).
smt(JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
                      auto.
while ((JWord.W64.(\ule) JWord.W64.zero ctx_offset) /\ (JWord.W64.(\ule) ctx_offset ctx_len) /\
       (JMemory.is_valid 18446744073709551616 JMemory.Glob.mem_v
       (JWord.W64.to_uint _ctx_ptr) (JWord.W64.to_uint _ctx_len)) /\
        ctx_ptr = _ctx_ptr /\ ctx_len = _ctx_len).

auto .
if .
auto .
ecall (_keccakf1600_ref1_proof param_0 (BArray200.init_arr (JWord.W8.of_int 255))).
auto .
rewrite /is_init /=.
                 rewrite /is_valid.
                 progress.
smt(BArray200.init_arrP).
have resolve_addition : (JWord.W64.of_int(i0) =
                         JWord.W64.of_int
                        (JWord.W64.to_uint ctx_ptr{hr} + JWord.W64.to_uint ctx_offset{hr})).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
have wrap_to_uint : (JWord.W64.to_uint(JWord.W64.of_int i0) =
                     JWord.W64.to_uint(JWord.W64.of_int
                    (JWord.W64.to_uint ctx_ptr{hr} + JWord.W64.to_uint ctx_offset{hr}))).
smt().
have unwrap : (i0 = (JWord.W64.to_uint ctx_ptr{hr} + JWord.W64.to_uint ctx_offset{hr})).
move: wrap_to_uint.
rewrite JWord.W64.of_uintK.
rewrite JWord.W64.of_uintK.
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
smt(JWord.W64.to_uint_cmp).
smt(JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
                      smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
                      auto.
                 rewrite /is_valid.
                 progress.
have resolve_addition : (JWord.W64.of_int(i0) =
                         JWord.W64.of_int
                        (JWord.W64.to_uint ctx_ptr{hr} + JWord.W64.to_uint ctx_offset{hr})).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
have wrap_to_uint : (JWord.W64.to_uint(JWord.W64.of_int i0) =
                     JWord.W64.to_uint(JWord.W64.of_int
                    (JWord.W64.to_uint ctx_ptr{hr} + JWord.W64.to_uint ctx_offset{hr}))).
smt().
have unwrap : (i0 = (JWord.W64.to_uint ctx_ptr{hr} + JWord.W64.to_uint ctx_offset{hr})).
move: wrap_to_uint.
rewrite JWord.W64.of_uintK.
rewrite JWord.W64.of_uintK.
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
smt(JWord.W64.to_uint_cmp).
smt(JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
                
auto.

while (0 <= i <= 24).
  auto => /> /#.
auto.
while (0 <= i <= 24).
  auto => /> /#.
auto.
ecall (__keccak_init_ref1_proof param b_param).
auto .
                      rewrite /is_init /=.
                 smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp BArray200.init_arrP).
qed .

lemma __PRF_msg_proof _out _b_out _skprf _b_skprf _optrand _b_optrand _ctx_ptr _ctx_len _msg_ptr _msg_len :
      (__PRF_msg_spec _out _b_out _skprf _b_skprf _optrand _b_optrand
      _ctx_ptr _ctx_len _msg_ptr _msg_len).
proof.
rewrite /__PRF_msg_spec .
proc; auto .
ecall (pRF_msg_proof param_5 b_param param_4 (BArray24.init_arr
                                             (JWord.W8.of_int 255)) param_3 
       (BArray24.init_arr (JWord.W8.of_int 255)) param_2 param_1 param_0 param).
auto .
smt(BArray32.init_arrP BArray24.init_arrP).
qed .

lemma pRF_proof _out _b_out _pkseed _b_pkseed _skseed _b_skseed _adrs _b_adrs :
      (pRF_spec _out _b_out _pkseed _b_pkseed _skseed _b_skseed _adrs 
      _b_adrs).
proof.
rewrite /pRF_spec .
proc; auto .
ecall (a_N____squeeze_avx2_proof param_18 (BArray224.init_arr (JWord.W8.of_int 255)
                                          ) param_17 b_param param_16).
auto .
ecall (a_N____absorb_avx2_proof param_15 (BArray224.init_arr (JWord.W8.of_int 255)) 
       param_14 param_13 (BArray24.init_arr (JWord.W8.of_int 255)) param_12 
       param_11).
auto .
ecall (a_32____absorb_avx2_proof param_10 (BArray224.init_arr (JWord.W8.of_int 255)
                                          ) param_9 param_8 (
                                                            BArray32.init_arr
                                                            (JWord.W8.of_int 255)) 
       param_7 param_6).
auto .
ecall (__adrs_to_bytes_proof param_5 b_param_0 param_4 (BArray32.init_arr
                                                       (JWord.W8.of_int 255))).
auto .
ecall (a_N____absorb_avx2_proof param_3 b_param_1 param_2 param_1 (
                                                                  BArray24.init_arr
                                                                  (JWord.W8.of_int
                                                                  255)) 
       param_0 param).
auto .
ecall (__state_init_avx2_proof).
auto .
smt(BArray32.init_arrP BArray24.init_arrP BArray224.init_arrP).
qed .

lemma __PRF_proof _out _b_out _pkseed _b_pkseed _skseed _b_skseed _adrs _b_adrs :
      (__PRF_spec _out _b_out _pkseed _b_pkseed _skseed _b_skseed _adrs
      _b_adrs).
proof.
rewrite /__PRF_spec .
proc; auto .
ecall (pRF_proof param_2 b_param param_1 (BArray24.init_arr (JWord.W8.of_int 255)) 
       param_0 (BArray24.init_arr (JWord.W8.of_int 255)) param (BArray32.init_arr
                                                         (JWord.W8.of_int 255))).
auto .
smt(BArray224.init_arrP BArray32.init_arrP BArray24.init_arrP).
qed .

lemma f_proof _out _b_out _pkseed _b_pkseed _adrs _b_adrs :
      (f_spec _out _b_out _pkseed _b_pkseed _adrs _b_adrs).
proof.
rewrite /f_spec .
proc; auto .
ecall (a_N____squeeze_avx2_proof param_18 (BArray224.init_arr (JWord.W8.of_int 255)
                                          ) param_17 (BArray24.init_arr
                                                     (JWord.W8.of_int 255)) 
       param_16).
auto .
ecall (a_N____absorb_avx2_proof param_15 (BArray224.init_arr (JWord.W8.of_int 255)) 
       param_14 param_13 (BArray24.init_arr (JWord.W8.of_int 255)) param_12 
       param_11).
auto .
ecall (a_32____absorb_avx2_proof param_10 (BArray224.init_arr (JWord.W8.of_int 255)
                                          ) param_9 param_8 (
                                                            BArray32.init_arr
                                                            (JWord.W8.of_int 255)) 
       param_7 param_6).
auto .
ecall (__adrs_to_bytes_proof param_5 b_param param_4 (BArray32.init_arr
                                                     (JWord.W8.of_int 255))).
auto .
ecall (a_N____absorb_avx2_proof param_3 b_param_0 param_2 param_1 (
                                                                  BArray24.init_arr
                                                                  (JWord.W8.of_int
                                                                  255)) 
       param_0 param).
auto .
ecall (__state_init_avx2_proof).
auto .
smt(BArray224.init_arrP BArray32.init_arrP BArray24.init_arrP).
qed .

lemma __F_proof _out _b_out _pkseed _b_pkseed _adrs _b_adrs :
      (__F_spec _out _b_out _pkseed _b_pkseed _adrs _b_adrs).
proof.
rewrite /__F_spec .
proc; auto .
ecall (f_proof param_1 (BArray24.init_arr (JWord.W8.of_int 255)) param_0 (
                                                                   BArray24.init_arr
                                                                   (JWord.W8.of_int
                                                                   255)) 
       param (BArray32.init_arr (JWord.W8.of_int 255))).
auto .
smt(BArray224.init_arrP BArray32.init_arrP BArray24.init_arrP).
qed .

lemma h_proof _out _b_out _pkseed _b_pkseed _adrs _b_adrs _in1 _b_in1 _in2 _b_in2 :
      (h_spec _out _b_out _pkseed _b_pkseed _adrs _b_adrs _in1 _b_in1 
      _in2 _b_in2).
proof.
rewrite /h_spec .
proc; auto .
ecall (a_N____squeeze_avx2_proof param_23 (BArray224.init_arr (JWord.W8.of_int 255)
                                          ) param_22 b_param param_21).
auto .
ecall (a_N____absorb_avx2_proof param_20 (BArray224.init_arr (JWord.W8.of_int 255)) 
       param_19 param_18 (BArray24.init_arr (JWord.W8.of_int 255)) param_17 
       param_16).
auto .
ecall (a_N____absorb_avx2_proof param_15 (BArray224.init_arr (JWord.W8.of_int 255)) 
       param_14 param_13 (BArray24.init_arr (JWord.W8.of_int 255)) param_12 
       param_11).
auto .
ecall (a_32____absorb_avx2_proof param_10 (BArray224.init_arr (JWord.W8.of_int 255)
                                          ) param_9 param_8 (
                                                            BArray32.init_arr
                                                            (JWord.W8.of_int 255)) 
       param_7 param_6).
auto .
ecall (__adrs_to_bytes_proof param_5 b_param_0 param_4 (BArray32.init_arr
                                                       (JWord.W8.of_int 255))).
auto .
ecall (a_N____absorb_avx2_proof param_3 b_param_1 param_2 param_1 (
                                                                  BArray24.init_arr
                                                                  (JWord.W8.of_int
                                                                  255)) 
       param_0 param).
auto .
ecall (__state_init_avx2_proof).
auto .
smt(BArray224.init_arrP BArray32.init_arrP BArray24.init_arrP).
qed .

lemma __H_proof _out _b_out _pkseed _b_pkseed _adrs _b_adrs _in1 _b_in1 _in2 _b_in2 :
      (__H_spec _out _b_out _pkseed _b_pkseed _adrs _b_adrs _in1 _b_in1 
      _in2 _b_in2).
proof.
rewrite /__H_spec .
proc; auto .
ecall (h_proof param_3 b_param param_2 (BArray24.init_arr (JWord.W8.of_int 255)) 
       param_1 (BArray32.init_arr (JWord.W8.of_int 255)) param_0 (BArray24.init_arr
                                                           (JWord.W8.of_int 255)) 
       param (BArray24.init_arr (JWord.W8.of_int 255))).
auto .
smt(BArray224.init_arrP BArray32.init_arrP BArray24.init_arrP).
qed .

lemma t_len_proof _out _b_out _pkseed _b_pkseed _adrs _b_adrs _chains _b_chains :
      (t_len_spec _out _b_out _pkseed _b_pkseed _adrs _b_adrs _chains
      _b_chains).
proof.
rewrite /t_len_spec .
proc; auto .
ecall (a_N____squeeze_avx2_proof param_18 (BArray224.init_arr (JWord.W8.of_int 255)
                                          ) param_17 b_param param_16).
auto .
ecall (a_LENN____absorb_avx2_proof param_15 (BArray224.init_arr
                                            (JWord.W8.of_int 255)) param_14 
       param_13 (BArray1224.init_arr (JWord.W8.of_int 255)) param_12 param_11).
auto .
ecall (a_32____absorb_avx2_proof param_10 (BArray224.init_arr (JWord.W8.of_int 255)
                                          ) param_9 param_8 (
                                                            BArray32.init_arr
                                                            (JWord.W8.of_int 255)) 
       param_7 param_6).
auto .
ecall (__adrs_to_bytes_proof param_5 b_param_0 param_4 (BArray32.init_arr
                                                       (JWord.W8.of_int 255))).
auto .
ecall (a_N____absorb_avx2_proof param_3 b_param_1 param_2 param_1 (
                                                                  BArray24.init_arr
                                                                  (JWord.W8.of_int
                                                                  255)) 
       param_0 param).
auto .
ecall (__state_init_avx2_proof).
auto .
smt(BArray224.init_arrP BArray32.init_arrP BArray24.init_arrP BArray1224.init_arrP).
qed .

lemma __T_len_proof _out _b_out _pkseed _b_pkseed _adrs _b_adrs _chains _b_chains :
      (__T_len_spec _out _b_out _pkseed _b_pkseed _adrs _b_adrs _chains
      _b_chains).
proof.
rewrite /__T_len_spec .
proc; auto .
ecall (t_len_proof param_2 b_param param_1 (BArray24.init_arr (JWord.W8.of_int 255)
                                           ) param_0 (BArray32.init_arr
                                                     (JWord.W8.of_int 255)) 
       param (BArray1224.init_arr (JWord.W8.of_int 255))).
auto .
smt(BArray224.init_arrP BArray32.init_arrP BArray24.init_arrP BArray1224.init_arrP).
qed .

lemma t_k_proof _out _b_out _pkseed _b_pkseed _adrs _b_adrs _roots _b_roots :
      (t_k_spec _out _b_out _pkseed _b_pkseed _adrs _b_adrs _roots _b_roots).
proof.
rewrite /t_k_spec .
proc; auto .
ecall (a_N____squeeze_avx2_proof param_18 (BArray224.init_arr (JWord.W8.of_int 255)
                                          ) param_17 b_param param_16).
auto .
ecall (a_KN____absorb_avx2_proof param_15 (BArray224.init_arr (JWord.W8.of_int 255)
                                          ) param_14 param_13 (
                                                              BArray408.init_arr
                                                              (JWord.W8.of_int 255)
                                                              ) param_12 
       param_11).
auto .
ecall (a_32____absorb_avx2_proof param_10 (BArray224.init_arr (JWord.W8.of_int 255)
                                          ) param_9 param_8 (
                                                            BArray32.init_arr
                                                            (JWord.W8.of_int 255)) 
       param_7 param_6).
auto .
ecall (__adrs_to_bytes_proof param_5 b_param_0 param_4 (BArray32.init_arr
                                                       (JWord.W8.of_int 255))).
auto .
ecall (a_N____absorb_avx2_proof param_3 b_param_1 param_2 param_1 (
                                                                  BArray24.init_arr
                                                                  (JWord.W8.of_int
                                                                  255)) 
       param_0 param).
auto .
ecall (__state_init_avx2_proof).
auto .
smt(BArray224.init_arrP BArray32.init_arrP BArray24.init_arrP BArray408.init_arrP).
qed .

lemma __T_k_proof _out _b_out _pkseed _b_pkseed _adrs _b_adrs _roots _b_roots :
      (__T_k_spec _out _b_out _pkseed _b_pkseed _adrs _b_adrs _roots 
      _b_roots).
proof.
rewrite /__T_k_spec .
proc; auto .
ecall (t_k_proof param_2 b_param param_1 (BArray24.init_arr (JWord.W8.of_int 255)) 
       param_0 (BArray32.init_arr (JWord.W8.of_int 255)) param (BArray408.init_arr
                                                         (JWord.W8.of_int 255))).
auto .
smt(BArray224.init_arrP BArray32.init_arrP BArray24.init_arrP BArray408.init_arrP).
qed .

lemma __copy_nbytes_proof _out _b_out _in _b_in :
      (__copy_nbytes_spec _out _b_out _in _b_in).
proof.
rewrite /__copy_nbytes_spec .
proc; auto .
while (0 <= i <= 24 /\ BArray24.is_init b_out 0 i /\ BArray24.is_init b_in 0 24).
  auto => /> &hr h0 h1 hb hin hi.
  split; 1: smt(). move=> _.
  split; 1: smt().
  by apply BArray24.is_init_set_last.
auto => />; smt().
qed.



lemma __memcmp_proof _a _b_a _b _b_b : (__memcmp_spec _a _b_a _b _b_b).
proof.
rewrite /__memcmp_spec .
proc; auto .
while (0 <= i /\ i <= 32).
auto .
smt().
auto .
qed .


lemma baseb_wots_m____base_b_proof _baseb _b_baseb _input _b_input :
      (baseb_wots_m____base_b_spec _baseb _b_baseb _input _b_input).
proof.
rewrite /baseb_wots_m____base_b_spec .
proc; auto .
while (0 <= out /\ out <= 48 /\
      ((1 <= out) => (BArray192.is_init b_baseb 0 (out * 4))) /\
      (0 <= JWord.W32.to_uint bits) /\ ((JWord.W32.to_uint bits) < 8) /\
      (0 <= JWord.W64.to_uint in_0) /\ ((JWord.W64.to_uint in_0) <= 24) /\
      ((8 * JWord.W64.to_uint in_0) = (4 * out + JWord.W32.to_uint bits)) /\
      (forall (k : int),
       (0 <= k /\ k < out) =>
       JWord.W32.to_uint (BArray192.get32d baseb (4 * k)) < 16)).
auto.
while ((0 <= JWord.W32.to_uint bits) /\ ((JWord.W32.to_uint bits) <= 8) /\
      (0 <= JWord.W64.to_uint in_0) /\ ((JWord.W64.to_uint in_0) <= 24) /\
      ((8 * JWord.W64.to_uint in_0) = (4 * out + JWord.W32.to_uint bits))  /\ out < 48).
        auto.
        progress; first 5
        smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
        rewrite /JWord.W64.(+) !JWord.W64.of_uintK /JWord.W32.(+) JWord.W32.of_uintK.
        smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
        auto.
        progress; first 7
        smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp BArray192.init_arrP BArray192.is_init_cell_set32d).
        move: H8.
        rewrite /JWord.W32.(\ult) /JWord.W32.(\ule) /JWord.W32.(+) /JWord.W32.ulift2 /JWord.W32.([-]) /JWord.W32.ulift1 !JWord.W32.of_uintK.
        move: H9.
        move: H11.
        rewrite /JWord.W32.(\ult).
        rewrite JWord.W32.of_uintK.
        smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
        move: H14.
        rewrite /JWord.W32.(\ult) /JWord.W32.(+) /JWord.W32.([-]) !JWord.W32.of_uintK.
        have : (((JWord.W32.to_uint bits0) + 4294967292) %% 4294967296) = JWord.W32.to_uint bits0 - 4.
        move: H9.
        move: H11.
        rewrite /JWord.W32.(\ult).
        rewrite JWord.W32.of_uintK.
        smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
        smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
        rewrite /JWord.W32.(\ult).
        have : (forall (w : JWord.W64.t), (JWord.W64.(\ult) (JWord.W64.(`&`) w (JWord.W64.of_int 15))
        (JWord.W64.of_int 16))).
      rewrite /JWord.W64.(\ult).
      rewrite JWord.W64.of_uintK.
      have : 15 = (2^4)-1.
    smt().
    move: JWord.W64.to_uint_and_mod.
    move => hkeq h15eq w.
    have temp := hkeq 4 w _.
    smt().
    smt().
    move => less_than_16_after_mask.
    case : (k < out{hr}).
    smt(BArray192.get_set32dE).
    smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp BArray192.get_set32E_eq).
    auto.
          rewrite /JWord.W32.(\ult).
    progress.
          smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
          rewrite and_iota.
          smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
          smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
          rewrite and_iota.
          rewrite /JUtils.(`<<`).
          smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
qed.

lemma baseb_wots_c____base_b_proof _baseb _b_baseb _input _b_input :
      (baseb_wots_c____base_b_spec _baseb _b_baseb _input _b_input).
proof.
rewrite /baseb_wots_c____base_b_spec .
proc; auto .
while (0 <= out /\ out <= 3 /\
      ((1 <= out) => (BArray12.is_init b_baseb 0 (out * 4))) /\
      (0 <= JWord.W32.to_uint bits) /\ ((JWord.W32.to_uint bits) < 8) /\
      (0 <= JWord.W64.to_uint in_0) /\ (JWord.W64.to_uint in_0 <= 3) /\
      ((8 * JWord.W64.to_uint in_0) = (4 * out + JWord.W32.to_uint bits)) /\
      (forall (k : int),
      (0 <= k /\ k < out) =>
       JWord.W32.to_uint (BArray12.get32d baseb (4 * k)) < 16)).
auto .
while ((0 <= JWord.W32.to_uint bits) /\ (JWord.W32.to_uint bits <= 8) /\
      (0 <= JWord.W64.to_uint in_0) /\ (JWord.W64.to_uint in_0 <= 3) /\
      ((8 * JWord.W64.to_uint in_0) = (4 * out + JWord.W32.to_uint bits))  /\ out < 3).
auto .
        progress; first 5
        smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
        rewrite /JWord.W64.(+) !JWord.W64.of_uintK /JWord.W32.(+) JWord.W32.of_uintK.
        smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
        auto.
        progress;first 7
        smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp BArray12.init_arrP BArray12.is_init_cell_set32d).
        move: H8.
        rewrite /JWord.W32.(\ult) /JWord.W32.(\ule) /JWord.W32.(+) /JWord.W32.ulift2 /JWord.W32.([-]) /JWord.W32.ulift1 !JWord.W32.of_uintK.
        move: H9.
        move: H11.
        rewrite /JWord.W32.(\ult).
        rewrite JWord.W32.of_uintK.
        smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
        move: H14.
        rewrite /JWord.W32.(\ult) /JWord.W32.(+) /JWord.W32.([-]) !JWord.W32.of_uintK.
        have : (((JWord.W32.to_uint bits0) + 4294967292) %% 4294967296) = JWord.W32.to_uint bits0 - 4.
        move: H9.
        move: H11.
        rewrite /JWord.W32.(\ult).
        rewrite JWord.W32.of_uintK.
        smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
        smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
        rewrite /JWord.W32.(\ult).
        have : (forall (w : JWord.W64.t), (JWord.W64.(\ult) (JWord.W64.(`&`) w (JWord.W64.of_int 15))
        (JWord.W64.of_int 16))).
      rewrite /JWord.W64.(\ult).
      rewrite JWord.W64.of_uintK.
      have : 15 = (2^4)-1.
    smt().
    move: JWord.W64.to_uint_and_mod.
    move => hkeq h15eq w.
    have temp := hkeq 4 w _.
    smt().
    smt().
    move => less_than_16_after_mask.
    case : (k < out{hr}).
    smt(BArray12.get_set32dE).
    smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp BArray12.get_set32E_eq).
    auto.
          rewrite /JWord.W32.(\ult).
          progress.
          smt().
          rewrite and_iota.
          smt().
          smt().
          rewrite and_iota.
    rewrite /JUtils.(`<<`).
    smt().
qed.

lemma __csum_proof _msg _b_msg : (__csum_spec _msg _b_msg).
proof.
rewrite /__csum_spec .
proc; auto .
while (0 <= i /\ i <= 64).
auto .
smt().
auto .
qed .

lemma __chain_lengths_proof _lengths _b_lengths _msg _b_msg :
      (__chain_lengths_spec _lengths _b_lengths _msg _b_msg).
proof.
rewrite /__chain_lengths_spec .
proc; auto .
ecall (baseb_wots_c____base_b_proof param_3 b_param_0 param_2 b_param).
auto .
while (0 <= k /\ k <= 2 /\
       ((1 <= k) => (BArray2.is_init b_csum_basew (2 - k) k))).
auto .
rewrite /is_init /valid /=.
smt().
auto .
ecall (__csum_proof param_1 b_param_1).
auto .
ecall (baseb_wots_m____base_b_proof param_0 b_param_2 param (
                                                            BArray24.init_arr
                                                            (JWord.W8.of_int 255))).
auto .
rewrite /JWord.W32.(\ult).
progress.
smt(BArray32.init_arrP BArray24.init_arrP ).
smt(BArray192.init_arrP SBArray204_192.SBArray204_192.is_init_cell_get SBArray204_192.SBArray204_192.is_init_cell_set ).
smt().
rewrite and_iota.
simplify.
move => a b.

case : (a < 48).
move => case1.
rewrite /BArray204.is_init.
split.
smt().
                                                        move => c d e.
                                                        rewrite (SBArray204_12.SBArray204_12.is_init_cell_set ((SBArray204_192.SBArray204_192.set_sub b_lengths{hr} 0 result0.`2)) result1.`2 192).
smt(SBArray204_192.SBArray204_192.is_init_cell_set).
smt(SBArray204_12.SBArray204_12.Asmall.init_arrP BArray32.init_arrP SBArray204_12.SBArray204_12.is_init_cell_set).
smt(BArray192.init_arrP SBArray204_192.SBArray204_192.is_init_cell_set SBArray204_12.SBArray204_12.Asmall.init_arrP BArray32.init_arrP SBArray204_12.SBArray204_12.is_init_cell_set).

rewrite and_iota.
rewrite /JUtils.(`<<`).
simplify.
move => a b.

case : (a < 48).
move => case1.
rewrite SBArray204_12.SBArray204_12.get32d_set_sub_out.
smt().
rewrite SBArray204_192.SBArray204_192.get32d_set_sub_in.
smt().
move : H5.
rewrite and_iota.
rewrite /JUtils.(`<<`).
smt().

move => case2.
rewrite SBArray204_12.SBArray204_12.get32d_set_sub_in.
smt().
move : H17.
rewrite and_iota.
rewrite /JUtils.(`<<`).
have : ((4 * a - 192)) = (4 * (a - 48)).
smt().
move => aux.
rewrite aux.
smt().
qed .

lemma chain_proof _out _b_out _i _steps _pkseed _b_pkseed _adrs _b_adrs :
      (chain_spec _out _b_out _i _steps _pkseed _b_pkseed _adrs _b_adrs).
proof.
rewrite /chain_spec .
proc; auto .
while (JWord.W32.(\ule) i t).
auto .
ecall (__F_proof param_3 (BArray24.init_arr (JWord.W8.of_int 255)) param_2 
       (BArray24.init_arr (JWord.W8.of_int 255)) param_1 (BArray32.init_arr
                                                   (JWord.W8.of_int 255))).
auto .
ecall (__adrs_set_hash_addr_proof param_0 (BArray32.init_arr (JWord.W8.of_int 255)) 
       param).
auto .
progress; try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
smt(BArray32.init_arrP BArray24.init_arrP).
move: H0.
rewrite /JWord.W32.(\ult).
rewrite /JWord.W32.(\ule).
rewrite /JWord.W32.(+).
rewrite /JWord.W32.ulift2.
rewrite JWord.W32.of_uintK.
rewrite JWord.W32.of_uintK.
smt(JWord.W32.to_uint_cmp).
auto .
progress.
rewrite /JWord.W32.(\ule).
rewrite /JWord.W32.(+).
rewrite /JWord.W32.ulift2.
rewrite JWord.W32.of_uintK.
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
rewrite /JWord.W32.(\ule).
rewrite /JWord.W32.(+).
rewrite /JWord.W32.ulift2.
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp BArray32.init_arrP BArray24.init_arrP).
smt(BArray32.init_arrP BArray24.init_arrP).
qed .

lemma __chain_proof _out _b_out _i _steps _pkseed _b_pkseed _adrs _b_adrs :
      (__chain_spec _out _b_out _i _steps _pkseed _b_pkseed _adrs _b_adrs).
proof.
rewrite /__chain_spec .
proc; auto .
ecall (chain_proof param_3 (BArray24.init_arr (JWord.W8.of_int 255)) param_2 
       param_1 param_0 (BArray24.init_arr (JWord.W8.of_int 255)) param (
                                                                 BArray32.init_arr
                                                                 (JWord.W8.of_int
                                                                 255))).
auto .
progress.
rewrite /JWord.W32.(\ule).
rewrite /JWord.W32.(+).
rewrite /JWord.W32.ulift2.
smt(BArray32.init_arrP BArray24.init_arrP).
smt(BArray32.init_arrP BArray24.init_arrP).
smt(BArray32.init_arrP BArray24.init_arrP).
qed .

lemma wots_pkgen_proof _pk _b_pk _skseed _b_skseed _pkseed _b_pkseed _adrs _b_adrs :
      (wots_pkgen_spec _pk _b_pk _skseed _b_skseed _pkseed _b_pkseed 
      _adrs _b_adrs).
proof.
rewrite /wots_pkgen_spec .
proc; auto .
ecall (__T_len_proof param_26 b_param_0 param_25 (BArray24.init_arr
                                                 (JWord.W8.of_int 255)) param_24 
       (BArray32.init_arr (JWord.W8.of_int 255)) param_23 b_param).
auto .
ecall (__adrs_set_key_pair_addr_proof param_22 (BArray32.init_arr
                                               (JWord.W8.of_int 255)) param_21).
auto .
ecall (__adrs_set_type_and_clear_proof param_20 (BArray32.init_arr
                                                (JWord.W8.of_int 255)) param_19).
auto .
while ((JWord.W32.(\ule) JWord.W32.zero idx_chain) /\
      (JWord.W32.(\ule) idx_chain (JWord.W32.of_int 51)) /\
      (JWord.W64.to_uint chain_addr = (JWord.W32.to_uint idx_chain) * 24) /\
      (BArray1224.is_init b_chains 0 (51 * 24))).
auto .
ecall (__chain_proof param_18 b_param_1 param_17 param_16 param_15 (
                                                                   BArray24.init_arr
                                                                   (JWord.W8.of_int
                                                                   255)) 
       param_14 (BArray32.init_arr (JWord.W8.of_int 255))).
auto .
ecall (__adrs_set_chain_addr_proof param_13 (BArray32.init_arr
                                            (JWord.W8.of_int 255)) param_12).
auto .
progress; try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
smt(BArray32.init_arrP BArray24.init_arrP).
smt(JWord.W64.to_uint_cmp).
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
smt(SBArray1224_24.SBArray1224_24.is_init_cell_get).
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
rewrite /JWord.W64.(+).
rewrite /JWord.W32.(+).
rewrite /JWord.W64.ulift2.
rewrite /JWord.W32.ulift2.
rewrite JWord.W64.of_uintK.
rewrite JWord.W64.of_uintK.
rewrite JWord.W32.of_uintK.
rewrite JWord.W32.of_uintK.
smt().
smt(SBArray1224_24.SBArray1224_24.is_init_cell_set).
                       
auto .
while (((JWord.W32.(\ule) JWord.W32.zero idx_chain) /\
      (JWord.W32.(\ule) idx_chain (JWord.W32.of_int 51)) /\
      (JWord.W64.to_uint chain_addr = (JWord.W32.to_uint idx_chain) * 24) /\
      (BArray1224.is_init b_chains 0 (JWord.W64.to_uint chain_addr)))).
auto .
ecall (__PRF_proof param_11 b_param_2 param_10 (BArray24.init_arr
                                               (JWord.W8.of_int 255)) param_9 
       (BArray24.init_arr (JWord.W8.of_int 255)) param_8 (BArray32.init_arr
                                                   (JWord.W8.of_int 255))).
auto .
ecall (__adrs_set_chain_addr_proof param_7 (BArray32.init_arr (JWord.W8.of_int 255)
                                           ) param_6).
auto .
progress; try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
smt(BArray32.init_arrP BArray24.init_arrP).
smt(JWord.W64.to_uint_cmp).
move : H3.
rewrite /JWord.W32.(\ult).
smt().
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
rewrite /JWord.W64.(+).
rewrite /JWord.W32.(+).
rewrite /JWord.W64.ulift2.
rewrite /JWord.W32.ulift2.
rewrite JWord.W64.of_uintK.
rewrite JWord.W64.of_uintK.
rewrite JWord.W32.of_uintK.
rewrite JWord.W32.of_uintK.
smt().
rewrite /BArray1224.is_init.
move => a b c.
rewrite (SBArray1224_24.SBArray1224_24.is_init_cell_set b_chains{hr} (BArray24.init_arr (JWord.W8.of_int 255)) (JWord.W64.to_uint chain_addr{hr}) a).
case : (JWord.W64.to_uint chain_addr{hr} <= a).
have : ((true && a < 24 + JWord.W64.to_uint chain_addr{hr}) /\ 0 <= a < 1224) = true.
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
smt().
smt().

auto .
ecall (__adrs_set_key_pair_addr_proof param_5 (BArray32.init_arr
                                              (JWord.W8.of_int 255)) param_4).
auto .
ecall (__adrs_get_key_pair_addr_proof param_3 (BArray32.init_arr
                                              (JWord.W8.of_int 255))).
auto .
ecall (__adrs_set_type_and_clear_proof param_2 (BArray32.init_arr
                                               (JWord.W8.of_int 255)) param_1).
auto .
ecall (__adrs_clone_proof param_0 b_param_3 param (BArray32.init_arr
                                                  (JWord.W8.of_int 255))).
auto .
progress; try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
smt(BArray32.init_arrP BArray24.init_arrP).
smt(BArray1224.init_arrP).
move : H17.
rewrite /JWord.W32.(\ult).
smt().
qed .

lemma __wots_pkgen_proof _pk _b_pk _skseed _b_skseed _pkseed _b_pkseed _adrs _b_adrs :
      (__wots_pkgen_spec _pk _b_pk _skseed _b_skseed _pkseed _b_pkseed 
      _adrs _b_adrs).
proof.
rewrite /__wots_pkgen_spec .
proc; auto .
ecall (wots_pkgen_proof param_2 b_param param_1 (BArray24.init_arr
                                                (JWord.W8.of_int 255)) param_0 
       (BArray24.init_arr (JWord.W8.of_int 255)) param (BArray32.init_arr
                                                 (JWord.W8.of_int 255))).
auto .
smt(BArray32.init_arrP BArray24.init_arrP).
qed .

lemma wots_sign_proof _sig_wots _b_sig_wots _m _b_m _skseed _b_skseed _pkseed _b_pkseed _adrs _b_adrs :
      (wots_sign_spec _sig_wots _b_sig_wots _m _b_m _skseed _b_skseed 
      _pkseed _b_pkseed _adrs _b_adrs).
proof.
rewrite /wots_sign_spec .
proc; auto .
while ((JWord.W32.(\ule) JWord.W32.zero idx_chain) /\ (JWord.W32.(\ule) idx_chain (JWord.W32.of_int 51))
/\ (BArray1224.is_init b_sig_wots 0 1224) /\
(JWord.W64.(\ule) JWord.W64.zero chain_addr) /\ (JWord.W64.(\ule) chain_addr (JWord.W64.of_int 1224))
/\ 
chain_addr = JWord.W64.of_int ((JWord.W32.to_uint idx_chain) * 24) /\
BArray204.is_init b_lengths 0 204).
auto .
ecall (__chain_proof param_20 b_param param_19 param_18 param_17 (
                                                                 BArray24.init_arr
                                                                 (JWord.W8.of_int
                                                                 255)) 
       param_16 (BArray32.init_arr (JWord.W8.of_int 255))).
                                                                   auto .
ecall (__adrs_set_chain_addr_proof param_15 (BArray32.init_arr
                                                                 (JWord.W8.of_int 255)) param_14).
auto .
                                              rewrite /=.
                                        progress.
smt(BArray32.init_arrP BArray24.init_arrP).
smt(JWord.W64.to_uint_cmp).
                                                               smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
                                                                               smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).

smt(JWord.W64.to_uint_cmp).
                                                               smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).

                                                               rewrite /BArray24.is_init.
                                                             move => a b c.
                                                             rewrite (SBArray1224_24.SBArray1224_24.is_init_cell_get b_sig_wots{hr} a (JWord.W64.to_uint
                                                                 (JWord.W64.of_int (JWord.W32.to_uint idx_chain{hr} * 24)))).
                                                                   trivial.
                                                                   smt().
                                                             smt().
                                                               try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          have : 2^32 = 4294967296.
                                                             smt().
                                                             move => mod.
                                                               
                                                             have klsdfsdf := JWord.W32.to_uint_cmp (BArray204.get32d lengths{hr}
     (4 * JWord.W64.to_uint (JWord.W2u32.zeroextu64 idx_chain{hr}))).
                                                smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray204.get32dE).

                                                                                      smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray204.get32dE SBArray1224_24.SBArray1224_24.is_init_cell_get).

                                                               smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray204.get32dE).
                                                                                                      
    smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray204.get32dE SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set).
                                                               smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray204.get32dE).
                                    
                                                               rewrite /JWord.W64.(\ule).
                                                               rewrite JWord.W64.of_uintK.
                                                               rewrite JWord.W64.of_uintK.
                                                             
                                                               smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray204.get32dE SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set).

                                                               rewrite /JWord.W32.(+).
                                                               rewrite /JWord.W32.ulift2.
                                                               rewrite JWord.W32.of_uintK.
                                                               rewrite JWord.W32.of_uintK.

                                                               try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          have : 2^32 = 4294967296.
                                                               smt().
                                                             move => mod.

                                                                                                       smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray204.get32dE SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set).
                                                             
auto .
while ((JWord.W32.(\ule) JWord.W32.zero idx_chain) /\ (JWord.W32.(\ule) idx_chain (JWord.W32.of_int 51))
/\ ((JWord.W32.(\ule) JWord.W32.one idx_chain)  =>
(BArray1224.is_init b_sig_wots 0 ((JWord.W32.to_uint idx_chain) * 24))) /\
(JWord.W64.(\ule) JWord.W64.zero chain_addr) /\ (JWord.W64.(\ule) chain_addr (JWord.W64.of_int 1224))
/\ chain_addr = JWord.W64.of_int ((JWord.W32.to_uint idx_chain) * 24)).
auto .
ecall (__PRF_proof param_13 b_param_0 param_12 (BArray24.init_arr
                                               (JWord.W8.of_int 255)) param_11 
       (BArray24.init_arr (JWord.W8.of_int 255)) param_10 (BArray32.init_arr
                                                    (JWord.W8.of_int 255))).
auto .
ecall (__adrs_set_chain_addr_proof param_9 (BArray32.init_arr (JWord.W8.of_int 255)
                                           ) param_8).
auto .
                                               rewrite /=.
                                         progress.
                                               smt(BArray32.init_arrP BArray24.init_arrP).
                                               smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray204.get32dE).
                                               smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray204.get32dE).
                                               try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray204.get32dE).
                                               smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray204.get32dE).
                                               move: H4.
                                         rewrite /JWord.W32.(\ult).
                                               rewrite /JWord.W32.(+).
                                               rewrite /JWord.W32.ulift2.
                                               rewrite JWord.W32.of_uintK.
                                               rewrite JWord.W32.of_uintK.
                                               rewrite JWord.W32.of_uintK.
                                               rewrite JWord.W64.of_uintK.
                                               try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          have : 2^32 = 4294967296.
                                               smt().
                                         move => mod.
                                               simplify.
                                         have: (JWord.W32.to_uint idx_chain{hr} * 24 %% 18446744073709551616) = (JWord.W32.to_uint idx_chain{hr} * 24).
                      smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                               BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE).

                                               have: ((JWord.W32.to_uint idx_chain{hr} + 1) %% 4294967296) = (JWord.W32.to_uint idx_chain{hr} + 1).
                                                               smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                               BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE).
                                         rewrite /is_init.
                                                               smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                               BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE).

                                               smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray204.get32dE).
                                               move: H4.
                                               rewrite /JWord.W32.(\ult).
                                               rewrite /JWord.W32.(\ule).
                                         rewrite /JWord.W64.(\ule).
                                         
                                               smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray204.get32dE).
                                               rewrite /JWord.W32.(+).
                                               rewrite /JWord.W32.ulift2.
                                               rewrite JWord.W32.of_uintK.
                                               rewrite JWord.W32.of_uintK.
                                               simplify.
                                               have : ((JWord.W32.to_uint idx_chain{hr} + 1) %% 4294967296 * 24) = ((JWord.W32.to_uint idx_chain{hr} + 1) * 24).
                                         
                                         
                                                               smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                               BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE).

                                                                                                       smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                               BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE).
                                         
                                         
auto .
ecall (__adrs_set_key_pair_addr_proof param_7 (BArray32.init_arr
                                              (JWord.W8.of_int 255)) param_6).
auto .
ecall (__adrs_get_key_pair_addr_proof param_5 (BArray32.init_arr
                                              (JWord.W8.of_int 255))).
auto .
ecall (__adrs_set_type_and_clear_proof param_4 (BArray32.init_arr
                                               (JWord.W8.of_int 255)) param_3).
auto .
ecall (__adrs_clone_proof param_2 b_param_1 param_1 (BArray32.init_arr
                                                    (JWord.W8.of_int 255))).
auto .
ecall (__chain_lengths_proof param_0 b_param_2 param (BArray24.init_arr
                                                     (JWord.W8.of_int 255))).
auto .
                                                 progress.
                                                       smt(BArray32.init_arrP BArray24.init_arrP).

                                                       try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          case : ((JWord.W32.to_uint idx_chain0) = 51).
                                                 move => klkl.
                                                       move: H26.
                                                       rewrite /JWord.W64.(\ule).
                                                 rewrite /JWord.W32.(\ule).
                                                       rewrite JWord.W32.of_uintK.
                                                       simplify.
                                                 subst.
                                                 
                                                  
                                                  smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                                   BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE).
                                                 move => aux.
                                                 

                                                 have : JWord.W32.to_uint idx_chain0 <= (JWord.W32.to_uint (JWord.W32.of_int 51)).
                                                 
                                                                                                   smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                                   BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE).
                                                 move => aux2.
                                                   have : ! (JWord.W32.to_uint idx_chain0 < (JWord.W32.to_uint (JWord.W32.of_int 51))).
                                                   move : H24.
                                                 rewrite /JWord.W32.(\ult).
                                                   rewrite JWord.W32.of_uintK.
                                                 
                                                                                                   smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                                   BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE).
                                                 move => aux3.
                                                   have : (JWord.W32.to_uint idx_chain0) = (JWord.W32.to_uint (JWord.W32.of_int 51)).
                                                   move: aux2.
                                                   move: aux3.
                                                 rewrite JWord.W32.of_uintK.

                                                                                                                                                    smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                                   BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE).

                                                 smt().                                        
qed .

lemma __wots_sign_proof _sig_wots _b_sig_wots _m _b_m _skseed _b_skseed _pkseed _b_pkseed _adrs _b_adrs :
      (__wots_sign_spec _sig_wots _b_sig_wots _m _b_m _skseed _b_skseed
      _pkseed _b_pkseed _adrs _b_adrs).
proof.
rewrite /__wots_sign_spec .
proc; auto .
ecall (wots_sign_proof param_3 b_param param_2 (BArray24.init_arr
                                               (JWord.W8.of_int 255)) param_1 
       (BArray24.init_arr (JWord.W8.of_int 255)) param_0 (BArray24.init_arr
                                                   (JWord.W8.of_int 255)) param 
       (BArray32.init_arr (JWord.W8.of_int 255))).
auto .
smt(BArray32.init_arrP BArray24.init_arrP BArray1224.init_arrP).
qed .

lemma wots_pkfromsig_proof _pk_wots _b_pk_wots _sig_wots _b_sig_wots _m _b_m _pkseed _b_pkseed _adrs _b_adrs :
      (wots_pkfromsig_spec _pk_wots _b_pk_wots _sig_wots _b_sig_wots 
      _m _b_m _pkseed _b_pkseed _adrs _b_adrs).
proof.
rewrite /wots_pkfromsig_spec .
proc; auto .
ecall (__T_len_proof param_18 b_param_0 param_17 (BArray24.init_arr
                                                 (JWord.W8.of_int 255)) param_16 
       (BArray32.init_arr (JWord.W8.of_int 255)) param_15 b_param).
auto .
ecall (__adrs_set_key_pair_addr_proof param_14 (BArray32.init_arr
                                               (JWord.W8.of_int 255)) param_13).
auto .
ecall (__adrs_get_key_pair_addr_proof param_12 (BArray32.init_arr
                                               (JWord.W8.of_int 255))).
auto .
ecall (__adrs_set_type_and_clear_proof param_11 (BArray32.init_arr
                                                (JWord.W8.of_int 255)) param_10).
auto .
ecall (__adrs_clone_proof param_9 b_param_1 param_8 (BArray32.init_arr
                                                    (JWord.W8.of_int 255))).
auto .
while (JWord.W32.(\ule) JWord.W32.zero idx_chain /\ JWord.W32.(\ule) idx_chain (JWord.W32.of_int 51)
/\ (JWord.W64.(\ule) JWord.W64.zero chain_addr)
/\(JWord.W64.(\ule) chain_addr (JWord.W64.of_int 1224))
/\ chain_addr = JWord.W64.of_int ((JWord.W32.to_uint idx_chain) * 24)
/\ BArray1224.is_init b_sigvals 0 1224
/\ (forall (k : int), ((0 <= k /\ k < 51) =>
   (JWord.W32.to_uint (BArray204.get32d lengths (4 * k)) < 16)))
/\ (BArray204.is_init b_lengths 0 204)).
auto .
ecall (__chain_proof param_7 b_param_2 param_6 param_5 param_4 (
                                                               BArray24.init_arr
                                                               (JWord.W8.of_int 255
                                                               )) param_3 
       (BArray32.init_arr (JWord.W8.of_int 255))).
auto .
ecall (__adrs_set_chain_addr_proof param_2 (BArray32.init_arr (JWord.W8.of_int 255)
                                           ) param_1).
auto .
progress; try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
smt(BArray32.init_arrP BArray24.init_arrP).
smt(JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
smt(JWord.W64.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
smt(SBArray1224_24.SBArray1224_24.is_init_cell_get).
                                      
have : (JWord.W32.to_uint(BArray204.get32d lengths{hr}
       (4 * JWord.W64.to_uint (JWord.W2u32.zeroextu64 idx_chain{hr})))) <= (4 * 51).
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
move => first_summand.
have: JWord.W32.to_uint(JWord.W32.WRingA.(-) (JWord.W32.of_int 15)
      (BArray204.get32d lengths{hr}
      (4 * JWord.W64.to_uint (JWord.W2u32.zeroextu64 idx_chain{hr})))) < 16.

have : (JWord.W32.to_uint(JWord.W32.WRingA.(-) (JWord.W32.of_int 15)
       (BArray204.get32d lengths{hr}
       (4 * JWord.W64.to_uint (JWord.W2u32.zeroextu64 idx_chain{hr})))) < 16) =
       (JWord.W32.to_uint (JWord.W32.of_int 15) -
        JWord.W32.to_uint((BArray204.get32d lengths{hr}
       (4 * JWord.W64.to_uint (JWord.W2u32.zeroextu64 idx_chain{hr})))) < 16).

have : 2^32 = 4294967296.
smt().
move => mod32.
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
move => convert.
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
move => second_summand.
smt().
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).

rewrite /JWord.W32.(+).
rewrite /JWord.W32.ulift2.
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).

rewrite /JWord.W64.(\ule).
rewrite JWord.W64.of_uintK.
rewrite JWord.W64.of_uintK.
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).

rewrite /JWord.W32.(+).
rewrite /JWord.W32.ulift2.
have : 2^32 = 4294967296.
smt().
move => mod32.
smt(JWord.W32.of_uintK).
smt(SBArray1224_24.SBArray1224_24.is_init_cell_set).
                                         
auto .
while (0 <= j /\ j <= 1224 /\
      ((1 <= j) => (BArray1224.is_init b_sigvals 0 j))).
auto .
rewrite /is_init /=.
smt().
auto .
ecall (__chain_lengths_proof param_0 b_param_3 param (BArray24.init_arr
                                                     (JWord.W8.of_int 255))).
auto .
progress.
smt(BArray32.init_arrP BArray24.init_arrP).
smt().
move : H11.
rewrite and_iota.
rewrite /JUtils.(`<<`).
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
qed .

lemma __wots_pkfromsig_proof _pk_wots _b_pk_wots _sig_wots _b_sig_wots _m _b_m _pkseed _b_pkseed _adrs _b_adrs :
      (__wots_pkfromsig_spec _pk_wots _b_pk_wots _sig_wots _b_sig_wots 
      _m _b_m _pkseed _b_pkseed _adrs _b_adrs).
proof.
rewrite /__wots_pkfromsig_spec .
proc; auto .
ecall (wots_pkfromsig_proof param_3 b_param param_2 (BArray1224.init_arr
                                                    (JWord.W8.of_int 255)) 
       param_1 (BArray24.init_arr (JWord.W8.of_int 255)) param_0 (BArray24.init_arr
                                                           (JWord.W8.of_int 255)) 
       param (BArray32.init_arr (JWord.W8.of_int 255))).
auto .
smt(BArray1224.init_arrP BArray32.init_arrP BArray24.init_arrP).
qed .

lemma __tree_label_proof _i _z : (__tree_label_spec _i _z).
proof.
rewrite /__tree_label_spec .
proc; auto .
progress.
rewrite /JWord.W64.(\ule).
smt(JWord.W64.to_uint_cmp).
rewrite /JWord.W64.(\ule).
rewrite JWord.W64.of_uintK.
have : 2 ^ 32 = 4294967296.
smt().
move => mod32.
have : 2 ^ 10 = 1024.
smt().
move => mod5.

have :((JWord.W64.SHIFT.SHL_64 JWord.W64.one (JWord.W4u8.truncateu8 (JWord.W32.of_int 10))).`6) =
      (JWord.W64.of_int (2 ^ 10)).
rewrite /JWord.W4u8.truncateu8.
rewrite JWord.W32.of_uintK.
rewrite /JWord.W64.SHIFT.SHL_64.
rewrite /JWord.W64.shift_mask.
rewrite JWord.W8.of_uintK.
simplify.
rewrite JWord.W64.shlMP.
smt().
rewrite JWord.W64.shlMP.
smt().
smt().
move => part1.

have : ((JWord.W64.SHIFT.SHL_64 JWord.W64.one (JWord.W4u8.truncateu8
       (JWord.W32.WRingA.(-) (JWord.W32.of_int 10) z{hr}))).`6) =
       (JWord.W64.of_int(2 ^ (10 - (JWord.W32.to_uint z{hr})))).
rewrite /JWord.W4u8.truncateu8.
         rewrite /JWord.W64.SHIFT.SHL_64.
         rewrite /JWord.W64.shift_mask.
rewrite JWord.W8.of_uintK.
simplify.
rewrite JWord.W64.shlMP.
smt().
rewrite JWord.W64.shlMP.
smt(JWord.W32.of_uintK).
have lt5 : JWord.W32.(\ult) z{hr} (JWord.W32.of_int 10).
smt(JWord.W32.of_uintK).

have lol : (JWord.W32.to_uint (JWord.W32.WRingA.(-) (JWord.W32.of_int 10) z{hr})) =
            (10 - JWord.W32.to_uint z{hr}).
smt(JWord.W32.of_uintK).
smt(JWord.W32.of_uintK).
move => part2.
rewrite part1 part2.
have : (JWord.W64.WRingA.(-) (JWord.W64.of_int (2 ^ 10))
       (JWord.W64.of_int (2 ^ (10 - JWord.W32.to_uint z{hr})))) =
        JWord.W64.of_int ((2 ^ 10) - (2 ^ (10 - JWord.W32.to_uint z{hr}))).
smt().
move => aux.
rewrite aux.
have : (JUtils.(`<<`) 1 (JWord.W32.to_uint
       (JWord.W32.WRingA.(-) (JWord.W32.of_int 9) z{hr})) - 1) =
       (2 ^ (9 - (JWord.W32.to_uint z{hr})) - 1).
smt(JWord.W32.of_uintK).
move => aux2.
have : JWord.W32.to_uint i{hr} <= (2 ^ (9 - JWord.W32.to_uint z{hr}) - 1).
move : H6.
move : H0.
rewrite aux2.
rewrite /JWord.W32.(\ule).
rewrite JWord.W32.of_uintK.
rewrite JWord.W32.of_uintK.

have : ((2 ^ (9 - JWord.W32.to_uint z{hr}) - 1) %% 4294967296) =
       (2 ^ (9 - JWord.W32.to_uint z{hr}) - 1).
         rewrite /JWord.W32.(\ule).

         have := StdOrder.IntOrder.ler_weexpn2l 2 _ (9 - JWord.W32.to_uint z{hr}) 9 _.
         trivial.                                                                                    smt(JWord.W32.of_uintK).
         simplify.

       move => bound1.

         have := IntDiv.modz_small (2 ^ (9 - JWord.W32.to_uint z{hr}) - 1) 4294967296.
       move=> aux3.
         rewrite aux3.
         smt(StdOrder.IntOrder.expr_gt0).
       trivial.

         have := StdOrder.IntOrder.ler_weexpn2l 2 _ ((9 - JWord.W32.to_uint z{hr})) 9 _.
         trivial.
         smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
         simplify.
       move=> aux3.
         smt().
         rewrite /JWord.W2u32.zeroextu64.
         simplify.
         move => hi.
have hz : JWord.W32.to_uint z{hr} <= 9.
  move: H5; rewrite /JWord.W32.(\ule) JWord.W32.of_uintK /#.
have e : 2 ^ (10 - JWord.W32.to_uint z{hr}) = 2 * 2 ^ (9 - JWord.W32.to_uint z{hr}).
  rewrite (_: 10 - JWord.W32.to_uint z{hr} = (9 - JWord.W32.to_uint z{hr}) + 1) 1:/#.
  rewrite StdOrder.IntOrder.Domain.exprS /#.
have p : 0 < 2 ^ (9 - JWord.W32.to_uint z{hr}) by rewrite StdOrder.IntOrder.expr_gt0.
have ub : 2 ^ (9 - JWord.W32.to_uint z{hr}) <= 2 ^ 9.
  apply StdOrder.IntOrder.ler_weexpn2l; smt(JWord.W32.to_uint_cmp).
have ev : 2 ^ 9 = 512 by smt().
rewrite e JWord.W64.of_uintK IntDiv.modz_small; smt(JWord.W32.to_uint_cmp).
       
         have : 2^32 = 4294967296.
         smt().
         move => mod32.

         rewrite /JWord.W32.(+).
         rewrite /JWord.W32.ulift2.
         rewrite JWord.W32.of_uintK.
         rewrite JWord.W32.of_uintK.

         rewrite /JWord.W64.SHIFT.SHL_64.
         simplify.
         rewrite /JWord.W64.shift_mask.
         simplify.

         have : (JWord.W8.to_uint (JWord.W4u8.truncateu8 (JWord.W32.of_int 10)) %% 64 = 0) = false.
         rewrite /JWord.W4u8.truncateu8.
         smt().
         move => cond0.
         rewrite cond0.
         simplify.

         have : (JWord.W8.to_uint (JWord.W4u8.truncateu8 (JWord.W32.of_int
                (10 + JWord.W32.to_uint (JWord.W32.([-]) z{hr})))) %% 64 = 0) = false.
         rewrite /JWord.W4u8.truncateu8.
         smt(JWord.W32.of_uintK).
         move => cond1.
         rewrite cond1.

         rewrite JWord.W64.shlMP.
         smt().
         rewrite JWord.W64.shlMP.
         smt().
         rewrite JWord.W64.shlMP.
         smt().
         rewrite JWord.W64.shlMP.
         smt().

         rewrite /JWord.W32.([-]).
         rewrite /JWord.W32.ulift1.

         rewrite /JWord.W2u32.truncateu32.
         rewrite /JWord.W4u8.truncateu8.

         rewrite JWord.W32.of_uintK.
         rewrite JWord.W32.of_uintK.
         rewrite JWord.W32.of_uintK.
         rewrite JWord.W8.of_uintK.
         rewrite JWord.W8.of_uintK.

         rewrite /JWord.W2u32.zeroextu64.

         rewrite /JUtils.(`<<`).

         have : (0 <= JWord.W32.to_uint (JWord.W32.(+) (JWord.W32.of_int 10)
                (JWord.W32.of_int (- JWord.W32.to_uint z{hr})))) = true.
         smt(JWord.W32.of_uintK).
         move => cond2.
         rewrite cond2.

         simplify.
         rewrite JWord.W32.of_uintK.

         rewrite /JWord.W64.SHIFT.rflags_OF.
         simplify.
                  rewrite JWord.W64.of_uintK.
            have : ((10 - JWord.W32.to_uint z{hr}) %% 4294967296) = ((10 - JWord.W32.to_uint z{hr})).

                  smt(JWord.W32.of_uintK).
            move => temp.
                  rewrite temp.
              smt(JWord.W32.to_uint_cmp StdOrder.IntOrder.ler_weexpn2l StdOrder.IntOrder.expr_gt0).
qed.


section.

local lemma xn_shl (w : JWord.W32.t) : JWord.W32.to_uint w < 64 =>
  (JWord.W64.SHIFT.SHL_64 JWord.W64.one (JWord.W4u8.truncateu8 w)).`6 = JWord.W64.of_int (2 ^ JWord.W32.to_uint w).
proof.
move=> h.
rewrite /JWord.W4u8.truncateu8 /JWord.W64.SHIFT.SHL_64 /JWord.W64.shift_mask JWord.W8.of_uintK /=.
have m : JWord.W32.to_uint w %% 256 %% 64 = JWord.W32.to_uint w by smt(JWord.W32.to_uint_cmp).
rewrite m; case (JWord.W32.to_uint w = 0) => [-> /=|nz /=].
  rewrite /JWord.flags_w /=.
  by case: (JWord.rflags_undefined) => a b c d e.
rewrite /JWord.W64.SHIFT.rflags_OF /JWord.flags_w /=.
rewrite (_: JWord.W64.one = JWord.W64.of_int 1) // JWord.W64.shlMP; smt(JWord.W32.to_uint_cmp).
qed.

local op xn_lbl (n l : int) = 2 ^ 10 - 2 ^ (10 - l) + n.

local lemma xn_init_na a n : BArray24.is_init (BArray24.init_arr (JWord.W8.of_int 255)) a n.
proof. by move=> k _ _; apply (BArray24.init_arrP witness). qed.

local lemma xn_init_ad a n : BArray32.is_init (BArray32.init_arr (JWord.W8.of_int 255)) a n.
proof. by move=> k _ _; apply (BArray32.init_arrP witness). qed.

local lemma xn_set_mono (t : BArray24552.t) k a n :
  BArray24552.is_init t a n =>
  BArray24552.is_init (SBArray24552_24.SBArray24552_24.set_sub t k (BArray24.init_arr (JWord.W8.of_int 255))) a n.
proof.
move=> h j h1 h2; rewrite SBArray24552_24.SBArray24552_24.is_init_cell_set.
have := h j h1 h2; have := BArray24.init_arrP witness (j - k); smt().
qed.

local lemma xn_set_ext (t : BArray24552.t) k a m :
  0 <= k => k + 24 <= 24552 => k = a + m =>
  BArray24552.is_init t a m =>
  BArray24552.is_init (SBArray24552_24.SBArray24552_24.set_sub t k (BArray24.init_arr (JWord.W8.of_int 255))) a (m + 24).
proof.
move=> h0 h1 hk h j h2 h3; rewrite SBArray24552_24.SBArray24552_24.is_init_cell_set.
have := BArray24.init_arrP witness (j - k).
case: (j < k) => hjk; last by smt().
have := h j h2 _; smt().
qed.

local lemma xn_get (t : BArray24552.t) k a n :
  0 <= k => k + 24 <= 24552 => a <= k => k + 24 <= a + n =>
  BArray24552.is_init t a n =>
  BArray24.is_init (SBArray24552_24.SBArray24552_24.get_sub t k) 0 24.
proof.
move=> h0 h1 h2 h3 h j hj1 hj2.
rewrite SBArray24552_24.SBArray24552_24.is_init_cell_get 1,2:/#.
apply h; smt().
qed.
local lemma xn_bnd (I Z L : int) : 0 <= L <= Z => Z <= 9 => 0 <= I < 2 ^ (9 - Z) =>
  (I + 1) * 2 ^ (Z - L) <= 2 ^ (9 - L).
proof.
move=> [h0 h1] h2 [h3 h4].
have -> : 2 ^ (9 - L) = 2 ^ (9 - Z) * 2 ^ (Z - L).
  by rewrite -StdOrder.IntOrder.Domain.exprD_nneg /#.
apply StdOrder.IntOrder.ler_wpmul2r; smt(StdOrder.IntOrder.expr_gt0).
qed.

local lemma xn_pow_le (a b : int) : 0 <= a <= b => 2 ^ a <= 2 ^ b.
proof. move=> h; apply StdOrder.IntOrder.ler_weexpn2l => /#. qed.
local lemma xn_shl1 k : 0 <= k => JUtils.(`<<`) 1 k = 2 ^ k.
proof. by move=> h; rewrite /JUtils.(`<<`) h. qed.

local lemma xn_tl_pre (wn wl : JWord.W32.t) :
  JWord.W32.to_uint wl <= 9 => JWord.W32.to_uint wn <= 2 ^ (9 - JWord.W32.to_uint wl) - 1 =>
  ((JWord.W32.(\ule) JWord.W32.zero wn /\ JWord.W32.(\ule) JWord.W32.zero wl) /\
    JWord.W32.(\ule) wl (JWord.W32.of_int 9)) /\
  JWord.W32.(\ule) wn (JWord.W32.of_int (JUtils.(`<<`) 1 (JWord.W32.to_uint (JWord.W32.WRingA.(-) (JWord.W32.of_int 9) wl)) - 1)).
proof.
move=> h1 h2; rewrite !JWord.W32.uleE JWord.W32.to_uintB 1:JWord.W32.uleE 1:/# /=.
rewrite xn_shl1 1:/#.
have p8 := xn_pow_le (9 - JWord.W32.to_uint wl) 9 _; 1: smt(JWord.W32.to_uint_cmp).
have hp8 : 2 ^ 9 = 512 by smt().
rewrite JWord.W32.of_uintK IntDiv.modz_small; smt(JWord.W32.to_uint_cmp StdOrder.IntOrder.expr_gt0).
qed.

local lemma xn_tl_post (r : JWord.W64.t) (wn wl : JWord.W32.t) :
  JWord.W32.to_uint wl <= 9 => JWord.W32.to_uint wn < 2 ^ (9 - JWord.W32.to_uint wl) =>
  JWord.W64.(\ule) r (JWord.W64.of_int 1022) =>
  JWord.W2u32.truncateu32 r =
    JWord.W32.(+) (JWord.W32.of_int (JUtils.(`<<`) 1 10 - JUtils.(`<<`) 1 (JWord.W32.to_uint (JWord.W32.WRingA.(-) (JWord.W32.of_int 10) wl)))) wn =>
  JWord.W64.to_uint r = xn_lbl (JWord.W32.to_uint wn) (JWord.W32.to_uint wl).
proof.
move=> h1 h2 h3 h4.
have hr : JWord.W64.to_uint r <= 1022 by move: h3; rewrite JWord.W64.uleE JWord.W64.of_uintK.
have := congr1 JWord.W32.to_uint _ _ h4.
rewrite JWord.W2u32.to_uint_truncateu32 JWord.W32.to_uintB 1:JWord.W32.uleE 1:/# /=.
rewrite !xn_shl1 1,2:/#.
have p8 := xn_pow_le (9 - JWord.W32.to_uint wl) 9 _; 1: smt(JWord.W32.to_uint_cmp).
have p9 := xn_pow_le (10 - JWord.W32.to_uint wl) 10 _; 1: smt(JWord.W32.to_uint_cmp).
have hp8 : 2 ^ 9 = 512 by smt(). have hp9 : 2 ^ 10 = 1024 by smt(). have m32 : 2 ^ 32 = 4294967296 by smt().
have e : 2 ^ (10 - JWord.W32.to_uint wl) = 2 * 2 ^ (9 - JWord.W32.to_uint wl).
  rewrite (_: 10 - JWord.W32.to_uint wl = (9 - JWord.W32.to_uint wl) + 1) 1:/#.
  rewrite StdOrder.IntOrder.Domain.exprS; smt(JWord.W32.to_uint_cmp).
rewrite /xn_lbl JWord.W32.to_uintD_small JWord.W32.of_uintK; smt(JWord.W32.to_uint_cmp JWord.W64.to_uint_cmp IntDiv.modz_small StdOrder.IntOrder.expr_gt0).
qed.
lemma xmss_node_proof _root _b_root _skseed _b_skseed _i _z _pkseed _b_pkseed _adrs _b_adrs :
      (xmss_node_spec _root _b_root _skseed _b_skseed _i _z _pkseed _b_pkseed
      _adrs _b_adrs).
proof.
rewrite /xmss_node_spec .
proc; auto .
ecall (__copy_nbytes_proof param_27 b_param_0 param_26 b_param).
auto .
while (JWord.W32.to_uint z <= 9 /\
       JWord.W32.to_uint i < 2 ^ (9 - JWord.W32.to_uint z) /\
       JWord.W32.to_uint layer <= JWord.W32.to_uint z + 1 /\
       (1 <= JWord.W32.to_uint layer => b_node_addr /\
          JWord.W64.to_uint node_addr = 24 * xn_lbl ((JWord.W32.to_uint i + 1) * 2 ^ (JWord.W32.to_uint z - (JWord.W32.to_uint layer - 1)) - 1) (JWord.W32.to_uint layer - 1)) /\
       (forall x, 0 <= x < JWord.W32.to_uint layer =>
          BArray24552.is_init b_flat_tree (24 * xn_lbl (JWord.W32.to_uint i * 2 ^ (JWord.W32.to_uint z - x)) x) (24 * 2 ^ (JWord.W32.to_uint z - x)))).
auto.
while (JWord.W32.to_uint z <= 9 /\
       JWord.W32.to_uint i < 2 ^ (9 - JWord.W32.to_uint z) /\
       JWord.W32.to_uint layer <= JWord.W32.to_uint z /\
       JWord.W32.to_uint rightmost = JWord.W32.to_uint i * 2 ^ (JWord.W32.to_uint z - JWord.W32.to_uint layer) + 2 ^ (JWord.W32.to_uint z - JWord.W32.to_uint layer) /\
       JWord.W32.to_uint i * 2 ^ (JWord.W32.to_uint z - JWord.W32.to_uint layer) <= JWord.W32.to_uint node <= JWord.W32.to_uint rightmost /\
       (forall x, 0 <= x < JWord.W32.to_uint layer =>
          BArray24552.is_init b_flat_tree (24 * xn_lbl (JWord.W32.to_uint i * 2 ^ (JWord.W32.to_uint z - x)) x) (24 * 2 ^ (JWord.W32.to_uint z - x))) /\
       BArray24552.is_init b_flat_tree (24 * xn_lbl (JWord.W32.to_uint i * 2 ^ (JWord.W32.to_uint z - JWord.W32.to_uint layer)) (JWord.W32.to_uint layer))
           (24 * (JWord.W32.to_uint node - JWord.W32.to_uint i * 2 ^ (JWord.W32.to_uint z - JWord.W32.to_uint layer))) /\
       (JWord.W32.to_uint i * 2 ^ (JWord.W32.to_uint z - JWord.W32.to_uint layer) < JWord.W32.to_uint node => b_node_addr /\
          JWord.W64.to_uint node_addr = 24 * xn_lbl (JWord.W32.to_uint node - 1) (JWord.W32.to_uint layer))).
auto.
if.
auto.
ecall (__wots_pkgen_proof param_6 b_param_1 param_5 (BArray24.init_arr (JWord.W8.of_int 255)) param_4 (BArray24.init_arr (JWord.W8.of_int 255)) param_3 (BArray32.init_arr (JWord.W8.of_int 255))).
auto.
ecall (__adrs_set_key_pair_addr_proof param_2 (BArray32.init_arr (JWord.W8.of_int 255)) param_1).
auto.
ecall (__adrs_set_type_and_clear_proof param_0  (BArray32.init_arr (JWord.W8.of_int 255)) param).
auto.
move=> &hr [#] hz hi hlz hr hs hn hall hcur hna hlt hl0.
have L0 : JWord.W32.to_uint layer{hr} = 0 by rewrite hl0.
have hlt' : JWord.W32.to_uint node{hr} < JWord.W32.to_uint rightmost{hr} by move: hlt; rewrite /JWord.W32.(\ult).
have hb := xn_bnd (JWord.W32.to_uint i{hr}) (JWord.W32.to_uint z{hr}) 0 _ _ _; 1..3: smt(JWord.W32.to_uint_cmp).
have hp8 : 2 ^ (9 - 0) = 512 by smt().
have e1 : JWord.W64.to_uint (JWord.W64.( * ) (JWord.W2u32.zeroextu64 node{hr}) (JWord.W64.of_int 24)) = 24 * JWord.W32.to_uint node{hr}.
  rewrite JWord.W64.to_uintM_small JWord.W2u32.to_uint_zeroextu64 JWord.W64.of_uintK /=; smt(JWord.W32.to_uint_cmp).
have e2 : JWord.W32.to_uint (JWord.W32.(+) node{hr} JWord.W32.one) = JWord.W32.to_uint node{hr} + 1.
  rewrite JWord.W32.to_uintD_small /=; smt(JWord.W32.to_uint_cmp).
rewrite e1 e2 L0 /= ?xn_init_na ?xn_init_ad /=.
have hlb : forall n, xn_lbl n 0 = n by move=> n; rewrite /xn_lbl /#.
have bn : 24 * JWord.W32.to_uint node{hr} + 24 <= 24552 by smt().
move=> r0 h0; split; 1: done. move=> _ r1 h1; split; 1: done. move=> _.
split; 1: smt(JWord.W32.to_uint_cmp). move=> _. split; 1: smt(JWord.W32.to_uint_cmp). move=> _.
move=> r2 h2; split; 1: done. move=> _.
rewrite !hlb /=.
do 5! (split; 1: smt(JWord.W32.to_uint_cmp)).
split; 1: smt().
have -> : 24 * (JWord.W32.to_uint node{hr} + 1 - JWord.W32.to_uint i{hr} * 2 ^ JWord.W32.to_uint z{hr}) =
          24 * (JWord.W32.to_uint node{hr} - JWord.W32.to_uint i{hr} * 2 ^ JWord.W32.to_uint z{hr}) + 24 by smt().
apply xn_set_ext; 1..3: smt(JWord.W32.to_uint_cmp).
by move: hcur; rewrite L0 hlb /=.
auto.
ecall (__H_proof param_25 b_param_2 param_24 (BArray24.init_arr (JWord.W8.of_int 255)) param_23 (BArray32.init_arr (JWord.W8.of_int 255)) param_22 (BArray24.init_arr (JWord.W8.of_int 255)) param_21 (BArray24.init_arr (JWord.W8.of_int 255))).
auto.
ecall (__tree_label_proof param_20 param_19).
auto.
ecall (__adrs_set_tree_index_proof param_18 (BArray32.init_arr (JWord.W8.of_int 255)) param_17).
auto.
ecall (__adrs_set_tree_height_proof param_16 (BArray32.init_arr (JWord.W8.of_int 255)) param_15).
auto.
ecall (__adrs_set_type_and_clear_proof param_14 (BArray32.init_arr (JWord.W8.of_int 255)) param_13).
auto.
ecall (__copy_nbytes_proof param_12 b_param_4 param_11 b_param_3).
auto.
ecall (__copy_nbytes_proof param_10 b_param_6 param_9 b_param_5).
auto.
ecall (__tree_label_proof param_8 param_7).
auto.
move=> &hr [#] hz hi hlz hr hs hn hall hcur hna hlt hl0.
have hL1 : 1 <= JWord.W32.to_uint layer{hr}.
  case: (JWord.W32.to_uint layer{hr} = 0) => h; 2: smt(JWord.W32.to_uint_cmp).
  by move: hl0; rewrite JWord.W32.to_uint_eq h; smt(JWord.W32.to_uint0).
have hlt' : JWord.W32.to_uint node{hr} < JWord.W32.to_uint rightmost{hr} by move: hlt; rewrite /JWord.W32.(\ult).
have hb := xn_bnd (JWord.W32.to_uint i{hr}) (JWord.W32.to_uint z{hr}) (JWord.W32.to_uint layer{hr}) _ _ _; 1..3: smt(JWord.W32.to_uint_cmp).
have hNd : JWord.W32.to_uint node{hr} < 2 ^ (9 - JWord.W32.to_uint layer{hr}) by smt().
have p8 := xn_pow_le (9 - JWord.W32.to_uint layer{hr}) 9 _; 1: smt().
have hp8 : 2 ^ 9 = 512 by smt().
have e7 : JWord.W32.to_uint (JWord.W32.WRingA.(-) layer{hr} JWord.W32.one) = JWord.W32.to_uint layer{hr} - 1.
  rewrite JWord.W32.to_uintB 1:JWord.W32.uleE; smt(JWord.W32.to_uint1).
have e8 : JWord.W32.to_uint (JWord.W32.( * ) node{hr} (JWord.W32.of_int 2)) = 2 * JWord.W32.to_uint node{hr}.
  rewrite JWord.W32.to_uintM_small JWord.W32.of_uintK /=; smt(JWord.W32.to_uint_cmp).
have eL : 2 ^ (9 - (JWord.W32.to_uint layer{hr} - 1)) = 2 * 2 ^ (9 - JWord.W32.to_uint layer{hr}).
  rewrite (_: 9 - (JWord.W32.to_uint layer{hr} - 1) = (9 - JWord.W32.to_uint layer{hr}) + 1) 1:/#.
  rewrite StdOrder.IntOrder.Domain.exprS /#.
have eZ : 2 ^ (JWord.W32.to_uint z{hr} - (JWord.W32.to_uint layer{hr} - 1)) = 2 * 2 ^ (JWord.W32.to_uint z{hr} - JWord.W32.to_uint layer{hr}).
  rewrite (_: JWord.W32.to_uint z{hr} - (JWord.W32.to_uint layer{hr} - 1) = (JWord.W32.to_uint z{hr} - JWord.W32.to_uint layer{hr}) + 1) 1:/#.
  rewrite StdOrder.IntOrder.Domain.exprS /#.
split.
  by apply xn_tl_pre; rewrite ?e7 ?e8; smt().
move=> _ r0 hr0; case: (hr0) => [[_ hr0le] hr0eq].
have lr0 := xn_tl_post r0 _ _ _ _ hr0le hr0eq; 1,2: by rewrite ?e7 ?e8; smt().
rewrite e7 e8 in lr0.
have r0le : JWord.W64.to_uint r0 <= 1022 by move: hr0le; rewrite JWord.W64.uleE JWord.W64.of_uintK.
have m0 : JWord.W64.to_uint (JWord.W64.( * ) r0 (JWord.W64.of_int 24)) = 24 * JWord.W64.to_uint r0.
  rewrite JWord.W64.to_uintM_small JWord.W64.of_uintK /=; smt(JWord.W64.to_uint_cmp).
have e9 : JUtils.(`<<`) 1 10 = 1024 by rewrite xn_shl1.
have q9 := xn_pow_le (10 - (JWord.W32.to_uint layer{hr} - 1)) 10 _; 1: smt().
have hp9 : 2 ^ 10 = 1024 by smt().
have e10 : 2 ^ (10 - (JWord.W32.to_uint layer{hr} - 1)) = 4 * 2 ^ (9 - JWord.W32.to_uint layer{hr}).
  rewrite (_: 10 - (JWord.W32.to_uint layer{hr} - 1) = (9 - JWord.W32.to_uint layer{hr}) + 2) 1:/# StdOrder.IntOrder.Domain.exprD_nneg 1,2:/#; smt().
have q1 : 0 < 2 ^ (9 - JWord.W32.to_uint layer{hr}) by apply StdOrder.IntOrder.expr_gt0.
have r0b : JWord.W64.to_uint r0 + 2 <= 1022 by rewrite lr0 /xn_lbl e10; smt().
have q0 : 0 < 2 ^ (JWord.W32.to_uint z{hr} - JWord.W32.to_uint layer{hr}) by apply StdOrder.IntOrder.expr_gt0.
have hA := hall (JWord.W32.to_uint layer{hr} - 1) _; 1: smt().
rewrite eZ in hA.
have r0p32 : JWord.W64.to_uint (JWord.W64.(+) (JWord.W64.( * ) r0 (JWord.W64.of_int 24)) (JWord.W64.of_int 24)) = 24 * JWord.W64.to_uint r0 + 24.
  rewrite JWord.W64.to_uintD_small m0 JWord.W64.of_uintK /=; smt(JWord.W64.to_uint_cmp).
rewrite r0p32 m0 ?xn_init_na ?xn_init_ad /=.
split; 1: by move: hr0; rewrite e9. move=> _.
split; 1: smt(JWord.W64.to_uint_cmp). move=> _.
split.
  by apply (xn_get _ _ _ _ _ _ _ _ hA); rewrite ?lr0 /xn_lbl; smt(JWord.W32.to_uint_cmp StdOrder.IntOrder.expr_gt0).
move=> _ r1 [h1a h1b]; split; 1: done. move=> _.
split; 1: smt(JWord.W64.to_uint_cmp). move=> _.
split.
  by apply (xn_get _ _ _ _ _ _ _ _ hA); rewrite ?lr0 /xn_lbl; smt(JWord.W32.to_uint_cmp StdOrder.IntOrder.expr_gt0).
move=> _ r2 [h2a h2b]; split; 1: done. move=> _ r3 h3; split; 1: done. move=> _ r4 h4; split; 1: done. move=> _ r5 h5; split; 1: done. move=> _.
split; 1: by apply xn_tl_pre; smt(). move=> _.
move=> r6 hr6; case: (hr6) => [[_ hr6le] hr6eq].
have lr6 := xn_tl_post r6 _ _ _ _ hr6le hr6eq; 1,2: smt().
have r6le : JWord.W64.to_uint r6 <= 1022 by move: hr6le; rewrite JWord.W64.uleE JWord.W64.of_uintK.
have m6 : JWord.W64.to_uint (JWord.W64.( * ) r6 (JWord.W64.of_int 24)) = 24 * JWord.W64.to_uint r6.
  rewrite JWord.W64.to_uintM_small JWord.W64.of_uintK /=; smt(JWord.W64.to_uint_cmp).
have e2 : JWord.W32.to_uint (JWord.W32.(+) node{hr} JWord.W32.one) = JWord.W32.to_uint node{hr} + 1.
  rewrite JWord.W32.to_uintD_small /=; smt(JWord.W32.to_uint_cmp).
rewrite m6 e2 /=.
have eL9 : 2 ^ (10 - JWord.W32.to_uint layer{hr}) = 2 * 2 ^ (9 - JWord.W32.to_uint layer{hr}).
  rewrite (_: 10 - JWord.W32.to_uint layer{hr} = (9 - JWord.W32.to_uint layer{hr}) + 1) 1:/#.
  rewrite StdOrder.IntOrder.Domain.exprS /#.
have r6b : JWord.W64.to_uint r6 + 1 <= 1023 by rewrite lr6 /xn_lbl eL9; smt().
split; 1: by move: hr6; rewrite e9. move=> _.
split; 1: smt(JWord.W64.to_uint_cmp). move=> _. split; 1: smt(JWord.W64.to_uint_cmp). move=> _.
move=> r7 h7; split; 1: done. move=> _.
split; 1: done. split; 1: done. split; 1: done. split; 1: done.
split; 1: by split; [apply (StdOrder.IntOrder.ler_trans _ _ _ hs); smt() | move=> _; smt()].
split.
  by move=> x hx; apply xn_set_mono; apply hall.
split; last by rewrite lr6.
have -> : 24 * (JWord.W32.to_uint node{hr} + 1 - JWord.W32.to_uint i{hr} * 2 ^ (JWord.W32.to_uint z{hr} - JWord.W32.to_uint layer{hr})) =
          24 * (JWord.W32.to_uint node{hr} - JWord.W32.to_uint i{hr} * 2 ^ (JWord.W32.to_uint z{hr} - JWord.W32.to_uint layer{hr})) + 24 by smt().
apply xn_set_ext => //; 1,2: smt(JWord.W64.to_uint_cmp).
by rewrite lr6 /xn_lbl; ring.
auto => &hr [#] hz hi hl hna hall hle.
have hle' : JWord.W32.to_uint layer{hr} <= JWord.W32.to_uint z{hr} by move: hle; rewrite JWord.W32.uleE.
have eexp : JWord.W32.to_uint (JWord.W32.WRingA.(-) z{hr} layer{hr}) = JWord.W32.to_uint z{hr} - JWord.W32.to_uint layer{hr}.
  by rewrite JWord.W32.to_uintB // JWord.W32.uleE.
have hsh := xn_shl (JWord.W32.WRingA.(-) z{hr} layer{hr}) _; 1: by rewrite eexp; smt(JWord.W32.to_uint_cmp).
rewrite eexp in hsh; simplify; rewrite hsh.
have hb := xn_bnd (JWord.W32.to_uint i{hr}) (JWord.W32.to_uint z{hr}) (JWord.W32.to_uint layer{hr}) _ _ _; 1..3: smt(JWord.W32.to_uint_cmp).
have p8 := xn_pow_le (9 - JWord.W32.to_uint layer{hr}) 9 _; 1: smt(JWord.W32.to_uint_cmp).
have hp8 : 2 ^ 9 = 512 by smt().
have q0 : 0 < 2 ^ (JWord.W32.to_uint z{hr} - JWord.W32.to_uint layer{hr}) by apply StdOrder.IntOrder.expr_gt0.
have et : JWord.W32.to_uint (JWord.W2u32.truncateu32 (JWord.W64.of_int (2 ^ (JWord.W32.to_uint z{hr} - JWord.W32.to_uint layer{hr})))) = 2 ^ (JWord.W32.to_uint z{hr} - JWord.W32.to_uint layer{hr}).
  have pZ := xn_pow_le (JWord.W32.to_uint z{hr} - JWord.W32.to_uint layer{hr}) 9 _; 1: by split; smt(JWord.W32.to_uint_cmp).
  rewrite JWord.W2u32.to_uint_truncateu32 JWord.W64.of_uintK !IntDiv.modz_small; smt().
have en : JWord.W32.to_uint (JWord.W32.( * ) (JWord.W2u32.truncateu32 (JWord.W64.of_int (2 ^ (JWord.W32.to_uint z{hr} - JWord.W32.to_uint layer{hr})))) i{hr}) =
          JWord.W32.to_uint i{hr} * 2 ^ (JWord.W32.to_uint z{hr} - JWord.W32.to_uint layer{hr}).
  rewrite JWord.W32.to_uintM_small et; smt(JWord.W32.to_uint_cmp).
have er : JWord.W32.to_uint (JWord.W32.(+) (JWord.W2u32.truncateu32 (JWord.W64.of_int (2 ^ (JWord.W32.to_uint z{hr} - JWord.W32.to_uint layer{hr}))))
            (JWord.W32.( * ) (JWord.W2u32.truncateu32 (JWord.W64.of_int (2 ^ (JWord.W32.to_uint z{hr} - JWord.W32.to_uint layer{hr})))) i{hr})) =
          JWord.W32.to_uint i{hr} * 2 ^ (JWord.W32.to_uint z{hr} - JWord.W32.to_uint layer{hr}) + 2 ^ (JWord.W32.to_uint z{hr} - JWord.W32.to_uint layer{hr}).
  rewrite JWord.W32.to_uintD_small en et; smt(JWord.W32.to_uint_cmp).
rewrite en er /=.
split.
  do 3! (split; 1: done).
  split; 1: smt().
  split; 1: done.
  by move=> k h1 h2; smt().
move=> bft bna nd na hnlt [#] _ _ _ hs0 hn0 hall0 hcur0 hna0.
have hnd : JWord.W32.to_uint nd = JWord.W32.to_uint i{hr} * 2 ^ (JWord.W32.to_uint z{hr} - JWord.W32.to_uint layer{hr}) + 2 ^ (JWord.W32.to_uint z{hr} - JWord.W32.to_uint layer{hr}).
  move: hnlt; rewrite /JWord.W32.(\ult) er; smt().
have el1 : JWord.W32.to_uint (JWord.W32.(+) layer{hr} JWord.W32.one) = JWord.W32.to_uint layer{hr} + 1.
  rewrite JWord.W32.to_uintD_small /=; smt(JWord.W32.to_uint_cmp).
rewrite el1 /=.
do 2! (split; 1: done).
split; 1: smt().
split.
  move=> _; have [-> ->] := hna0 _; 1: smt().
  by rewrite hnd /=; congr; congr; ring.
move=> x hx; case: (x < JWord.W32.to_uint layer{hr}) => hxl; 1: by apply hall0; smt().
have -> : x = JWord.W32.to_uint layer{hr} by smt().
by move: hcur0; rewrite hnd; smt().
auto => /> &hr hadrs hpk h0i h0z hz8 hi.
have hzz : JWord.W32.to_uint _z <= 9 by move: hz8; rewrite JWord.W32.uleE JWord.W32.of_uintK.
have p8 := xn_pow_le (9 - JWord.W32.to_uint _z) 9 _; 1: smt(JWord.W32.to_uint_cmp).
have hp8 : 2 ^ 9 = 512 by smt().
have hii : JWord.W32.to_uint _i < 2 ^ (9 - JWord.W32.to_uint _z).
  move: hi; rewrite JWord.W32.uleE JWord.W32.to_uintB 1:JWord.W32.uleE 1:JWord.W32.of_uintK 1:/# JWord.W32.of_uintK /=.
  rewrite xn_shl1 1:/#; smt(JWord.W32.to_uint_cmp StdOrder.IntOrder.expr_gt0 IntDiv.modz_small).
split.
  smt(JWord.W32.to_uint_cmp).
move=> bft bna l na hnle _ _ hl1 hna hall.
have hlz : JWord.W32.to_uint l = JWord.W32.to_uint _z + 1 by move: hnle; rewrite JWord.W32.uleE; smt().
have [-> hna'] := hna _; 1: smt(JWord.W32.to_uint_cmp).
rewrite hlz /= in hna'.
have eZ : 2 ^ (10 - JWord.W32.to_uint _z) = 2 * 2 ^ (9 - JWord.W32.to_uint _z).
  rewrite (_: 10 - JWord.W32.to_uint _z = (9 - JWord.W32.to_uint _z) + 1) 1:/#.
  rewrite StdOrder.IntOrder.Domain.exprS; smt(JWord.W32.to_uint_cmp).
have hbd : JWord.W64.to_uint na + 24 <= 24552 by rewrite hna' /xn_lbl eZ; smt(JWord.W32.to_uint_cmp).
split; 1: done. move=> _.
split; 1: smt(JWord.W64.to_uint_cmp). move=> _.
move=> _; split.
  have hA := hall (JWord.W32.to_uint _z) _; 1: smt(JWord.W32.to_uint_cmp).
  move: hA; rewrite /= => hA.
  by apply (xn_get _ _ _ _ _ _ _ _ hA); rewrite ?hna'; smt(JWord.W64.to_uint_cmp).
by move=> _ r0 _; rewrite ?xn_init_na ?xn_init_ad.
qed.

end section.



lemma __xmss_node_proof _root _b_root _skseed _b_skseed _i _z _pkseed _b_pkseed _adrs _b_adrs :
      (__xmss_node_spec _root _b_root _skseed _b_skseed _i _z _pkseed
      _b_pkseed _adrs _b_adrs).
proof.
rewrite /__xmss_node_spec .
proc; auto .
ecall (xmss_node_proof param_4 b_param param_3 (BArray24.init_arr
                                               (JWord.W8.of_int 255)) param_2 
       param_1 param_0 (BArray24.init_arr (JWord.W8.of_int 255)) param (
                                                                 BArray32.init_arr
                                                                 (JWord.W8.of_int
                                                                 255))).
auto .
smt(BArray32.init_arrP BArray24.init_arrP).
qed .

section.
local lemma xs_pow_le k : 0 <= k <= 9 => 2 ^ k <= 512.
proof. move=> h; have := StdOrder.IntOrder.ler_weexpn2l 2 _ k 9 _; smt(). qed.
local lemma xs_pow_eq : 2 ^ 9 = 512.
proof. by []. qed.

lemma xmss_sign_proof _sig_xmss _b_sig_xmss _m _b_m _skseed _b_skseed _idx _pkseed _b_pkseed _adrs _b_adrs :
      (xmss_sign_spec _sig_xmss _b_sig_xmss _m _b_m _skseed _b_skseed 
      _idx _pkseed _b_pkseed _adrs _b_adrs).
proof.
rewrite /xmss_sign_spec .
proc; auto .
ecall (__wots_sign_proof param_13 b_param param_12 (BArray24.init_arr
                                                   (JWord.W8.of_int 255)) param_11 
       (BArray24.init_arr (JWord.W8.of_int 255)) param_10 (BArray24.init_arr
                                                    (JWord.W8.of_int 255)) 
       param_9 (BArray32.init_arr (JWord.W8.of_int 255))).
auto .
ecall (__adrs_set_key_pair_addr_proof param_8 (BArray32.init_arr
                                              (JWord.W8.of_int 255)) param_7).
auto .
ecall (__adrs_set_type_and_clear_proof param_6 (BArray32.init_arr
                                               (JWord.W8.of_int 255)) param_5).
                                                 auto .
while (JWord.W32.(\ule) JWord.W32.zero j /\ JWord.W32.(\ule) j (JWord.W32.of_int 9) /\
      (JWord.W64.(\ule) offset (JWord.W64.of_int (1224 + (JWord.W32.to_uint j) * 24))) /\
      (JWord.W64.(\ule) offset (JWord.W64.of_int (1440))) /\
      (k = JWord.W32.(`^`) (JWord.W32.of_int((JUtils.(`|>>`)
      (JWord.W32.to_uint idx) (JWord.W32.to_uint j)))) JWord.W32.one) /\
      (JWord.W32.(\ule) idx (JWord.W32.of_int (JUtils.(`<<`) 1 9 - 1))) /\
      (BArray1440.is_init b_sig_xmss 1224 ((JWord.W64.to_uint offset) - 1224)) /\
      (1224 <=  JWord.W64.to_uint offset) /\
      (offset = (JWord.W64.of_int (1224 + (JWord.W32.to_uint j) * 24)))).
auto .
ecall (__xmss_node_proof param_4 b_param_0 param_3 (BArray24.init_arr
                                                   (JWord.W8.of_int 255)) param_2 
       param_1 param_0 (BArray24.init_arr (JWord.W8.of_int 255)) param (
                                                                 BArray32.init_arr
                                                                 (JWord.W8.of_int
                                                                 255))).
                                                                   auto .
                                                          
                                                                   rewrite /is_init /valid /=.


                                                                   have : forall (x : JWord.W32.t), (JWord.W32."_.[_]" x 0 = true) => (JWord.W32."_.[_]" ((JWord.W32.(`^`)) x JWord.W32.one) 0 = false).


                      smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                             move => xor_one_lbt.

                                                               have : forall (x : JWord.W32.t), (JWord.W32."_.[_]" x 0 = false) => (JWord.W32."_.[_]" ((JWord.W32.(`^`)) x JWord.W32.one) 0 = true).
                                                                   smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                             move => xor_one_lbf.


          have xor_same_g0 : forall (x : JWord.W32.t) (i : int), i <> 0 => 
        JWord.W32."_.[_]"(JWord.W32.(`^`) x JWord.W32.one) i = JWord.W32."_.[_]" x i.
                                                                   smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                          
                                                               have : forall (w : JWord.W32.t), (JWord.W32."_.[_]" w 0 = true) => (JWord.W32.(`&`) w (JWord.W32.masklsb 1)) = JWord.W32.one.
                                                             move => w.
                                                             move => aux.
                                                               have := JWord.W32.wordP (JWord.W32.(`&`) w (JWord.W32.masklsb 1)) JWord.W32.one.

                                                             move => aux2.
                                                               apply aux2.
                                                             move => aux3 aux4.

                                                               have := JWord.W32.andwE w (JWord.W32.masklsb 1) aux3.
                                                             move => aux5.
                                                               rewrite aux5.
                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                             move => one_and_one_eq_one.

                                                                                                                            have : forall (w : JWord.W32.t), (JWord.W32."_.[_]" w 0 = false) => (JWord.W32.(`&`) w (JWord.W32.masklsb 1)) = JWord.W32.zero.
                                                             move => w.
                                                             move => aux.
                                                               have := JWord.W32.wordP (JWord.W32.(`&`) w (JWord.W32.masklsb 1)) JWord.W32.zero.

                                                             move => aux2.
                                                               apply aux2.
                                                             move => aux3 aux4.

                                                               have := JWord.W32.andwE w (JWord.W32.masklsb 1) aux3.
                                                             move => aux5.
                                                               rewrite aux5.
                                                                                                                            smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                             move => zero_and_one_eq_zero.

                                                               have : forall (x : JWord.W32.t), (JWord.W32.(`>>>`) x 1) = (JWord.W32.(`>>>`) ((JWord.W32.(`^`) x JWord.W32.one)) 1).
                                                             move => w.

                                                               have := JWord.W32.wordP (JWord.W32.(`>>>`) w 1) (JWord.W32.(`>>>`) (JWord.W32.(`^`) w JWord.W32.one) 1).
                                                             move => aux.
                                                               apply aux.
                                                             move => aux2 aux3.

                                                               have := JWord.W32.shrwE w 1 aux2.
                                                             move => aux4.
                   have := JWord.W32.shrwE ((JWord.W32.(`^`) w JWord.W32.one)) 1 aux2.
                                                             move => aux5.

                                                               have : ((0 <= aux2 < 32 && JWord.W32."_.[_]" w (aux2 + 1))) = (0 <= aux2 < 32 && JWord.W32."_.[_]" (JWord.W32.(`^`) w JWord.W32.one) (aux2 + 1)).

                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                             move => aux6.
                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                             move => shift_xor_eq.

                                                             have : forall (x : JWord.W32.t),
           JWord.W32.to_uint (JWord.W32.(`>>>`) x 1) =
                                                               JWord.W32.to_uint (JWord.W32.(`>>>`) (JWord.W32.(`^`) x JWord.W32.one) 1).
                                                                                  smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                                               BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg JWord.W32.xorwE JWord.W32.get_to_uint).
                                                             move => shift_xor_eq_uint.
                                                             
                 have : forall (x : JWord.W32.t),
           JWord.W32.to_uint x %/ 2 ^ 1 =
                                                               JWord.W32.to_uint (JWord.W32.(`^`) x JWord.W32.one) %/ 2 ^ 1.
                                                             move => w.
                                                               have := JWord.W32.to_uint_shr w 1.
                                                             move => part1.

                                                               have := JWord.W32.to_uint_shr ((JWord.W32.(`^`) w JWord.W32.one)) 1.
                                                             move => part2.

                                                               have := shift_xor_eq_uint w.
                                                               rewrite part1.
                                                               smt().
                                                               rewrite part2.
                                                               smt().
                                                               smt().
                                                             simplify.
                                                             
                                                             move => div2_xor_eq.
                                                            

          have : forall (x : JWord.W32.t), JWord.W32.to_uint ((JWord.W32.(`^`)) x JWord.W32.one) <=
                                                             (JWord.W32.to_uint x) + 1.
                                                             move => w.

                                                               case : (JWord.W32."_.[_]" w 0 = true).
                                                             move => case1.

                                                               have := JWord.W32.splitwE 1 ((JWord.W32.(`^`) w JWord.W32.one)).
                                                             move => aux.

                                                               have := zero_and_one_eq_zero ((JWord.W32.(`^`) w JWord.W32.one)).
                                                             move => aux2.
                                                               move : aux.
                                                               rewrite aux2.
                                                               have :=  xor_one_lbt.
                                                             move => aux3.
                                                               have :  (JWord.W32."_.[_]" (JWord.W32.(`^`) w JWord.W32.one) 0 = false).
                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                               smt().

                                                               have := JWord.W32.to_uint_shr ((JWord.W32.(`^`) w JWord.W32.one)) 1.
                                                             move => aux3.
                                                               rewrite aux3.
                                                               smt().
                                                               simplify.

                      have : (2 * (JWord.W32.to_uint (JWord.W32.(`^`) w JWord.W32.one) %/ 2)) <= (JWord.W32.to_uint (JWord.W32.(`^`) w JWord.W32.one)).
                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                             move => aux4.
                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                             move => case2.

                                                                                                                            have := JWord.W32.splitwE 1 ((JWord.W32.(`^`) w JWord.W32.one)).
                                                             move => aux.

                                                               have := one_and_one_eq_one ((JWord.W32.(`^`) w JWord.W32.one)).
                                                             move => aux2.
                                                               move : aux.
                                                               rewrite aux2.
                                                               have := xor_one_lbt w.
                                                             move => aux3.
                                                               have :  (JWord.W32."_.[_]" (JWord.W32.(`^`) w JWord.W32.one) 0 = true).
                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                               smt().

                                                               have := JWord.W32.to_uint_shr ((JWord.W32.(`^`) w JWord.W32.one)) 1.
                                                             move => aux3.
                                                               rewrite aux3.
                                                               smt().
                                                               simplify.

                      have : (2 * (JWord.W32.to_uint (JWord.W32.(`^`) w JWord.W32.one) %/ 2)) <= (JWord.W32.to_uint (JWord.W32.(`^`) w JWord.W32.one)).
                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                             move => aux4.
                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                             move => xor_one_bound.
                               have : forall (x : JWord.W32.t),
                                                               JWord.W32."_.[_]" x 0 = true => Int.odd (JWord.W32.to_uint x).

                                                             move => x hbit0.
have h := JWord.W32.get_to_uint x 0.
                                                               rewrite hbit0 in h.
                                                               move : h.
                                                             simplify.
                                                               smt(IntDiv.oddP).
                                                             move => lbt_odd.
                                                             

                              have : forall (x : JWord.W32.t),
                                                               JWord.W32."_.[_]" x 0 = false => !Int.odd (JWord.W32.to_uint x).

                                                             move => x hbit0.
have h := JWord.W32.get_to_uint x 0.
                                                               rewrite hbit0 in h.
                                                               move : h.
                                                             simplify.
                                                               smt(IntDiv.oddP).
                                                             move => lbf_nodd.

                                                               have : forall (x : JWord.W32.t) (i : int),
                                                             (JWord.W32.to_uint x <= i /\ Int.odd i /\ !Int.odd (JWord.W32.to_uint x)) =>
                                                             (JWord.W32.to_uint x <= i - 1).

                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one IntDiv.divzMDl IntDiv.oddW IntDiv.oddP).
                                                             move => nodd_odd_tight_bound.

                               
                                                                                                                

                                                               have : forall (n : int), Int.odd n => n %/ 2 = (n-1) %/ 2.
                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one IntDiv.divzMDl IntDiv.oddW).
                                                             move => odd_div2.

                                                               have :  forall (n x : int), (2 <= x) => n %/ (2 ^ x) = ((n %/ 2) %/ (2 ^ (x - 1))).

                                                             move => n x hx.
have hexp : 2 ^ x = 2 * 2 ^ (x-1).
  smt( StdOrder.IntOrder.Domain.exprS).
have h2pos : 0 < 2^(x-1) by smt(StdOrder.IntOrder.expr_gt0).
                                                               smt(IntDiv.divz_mulp).
                                                             move => exp_div_split.

                                                               have : forall (n x : int), (Int.odd n /\ 2 <= x) => n %/ (2 ^ x) = (n-1) %/ (2 ^ x).
                                                             move => n x idk.

                                                               have := exp_div_split n x.
                                                             move => aux.
                                                               rewrite aux.
                                                               smt().
                                                               have := odd_div2 n.
                                                             move => aux2.
                                                               rewrite aux2.
                                                             smt().

                           
                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one IntDiv.divzMDl IntDiv.oddW).
                                                             move => odd_div_exp.

   have : forall (x : JWord.W32.t), (JWord.W32."_.[_]" x 0 = true)  =>
                JWord.W32.to_uint((JWord.W32.(`^`) x JWord.W32.one)) = (JWord.W32.to_uint x) - 1.
                                                             move => w.

                                                               have := JWord.W32.splitwE 1 ((JWord.W32.(`^`) w JWord.W32.one)).
                                                             move => aux.
                                                               rewrite aux.
                                                               smt().
                                                             move => aux2.
                                                               have := zero_and_one_eq_zero ((JWord.W32.(`^`) w JWord.W32.one)).
                                                             move => aux3.
                                                               have := xor_one_lbt w.
                                                             move => aux4.
                                                             
                                                               rewrite aux3.
                                                             

                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one IntDiv.divzMDl IntDiv.oddW IntDiv.oddP).

                                                               have := shift_xor_eq_uint w.
                                                             move => aux5.
                                                               rewrite -aux5.
                                                               have := JWord.W32.to_uint_shr w 1.
                                                             move => aux6.
                                                               rewrite aux6.
                                                               smt().
                                                             
                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                             move => lbt_xor_minus_one.

                                                                                                                          progress.
  smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                                                   BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
                                                               smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                                                   BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
                                                               smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                                                   BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
                                                               smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                                                   BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
                                                               smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                                                   BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
                                                               smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                                                   BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
                                                             
                                                             
                                                             

                                                       
                                                                   move : H3.
                                                                   rewrite /JUtils.(`|>>`).
                                                                   rewrite /JUtils.(`<<`).
                                                             
                                                                   simplify.

                                                                   rewrite /JWord.W32.(\ule).
                                                                   rewrite /JWord.W32.(+).
                                                                   rewrite /JWord.W32.ulift2.
                                                                   rewrite /JWord.W32.([-]).
                                                                   rewrite /JWord.W32.ulift1.
                                                                   rewrite JWord.W32.of_uintK.
                                                                   rewrite JWord.W32.of_uintK.
                                                                   rewrite JWord.W32.of_uintK.
                                                                   rewrite JWord.W32.of_uintK.
                                                                   rewrite JWord.W32.of_uintK.
                                                                   simplify.


                                                                   have : ((9 + (- JWord.W32.to_uint j{hr}) %% 4294967296) %% 4294967296) = ((9 + (- JWord.W32.to_uint j{hr})) %% 4294967296).
                                                                                                                            smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                                                   BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
                                                             move => temp.
                                                             rewrite temp.

             have := IntDiv.modz_small ((9 - JWord.W32.to_uint j{hr})) 4294967296.
                                                             move => temp0.
                                                                   rewrite temp0.
                                                             
                                                               smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                                                   BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).

                                                             
                                                             
                                                                   case : ((JWord.W32.to_uint j{hr}) = 0).
                                                             move => case0.

                                                             have : (0 <= - JWord.W32.to_uint j{hr}) = true.
                                                               smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                                                   BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).

                                                             move => temp1.
                                                             rewrite temp1.
                                                                   simplify.
                               have : (0 <= 9 - JWord.W32.to_uint j{hr}) = true.
                                                                                                                            smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                                                   BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
                                                             move => temp2.
                                                                   rewrite temp2.
                                                               simplify.


case : (JWord.W32."_.[_]" ((JWord.W32.of_int
                                                                   (JWord.W32.to_uint idx{hr} * 2 ^ - JWord.W32.to_uint j{hr}))) 0 = true).
                                                             move => case1.
                                                             move => aux.

                                           have := lbt_xor_minus_one ((JWord.W32.of_int
                                                                 (JWord.W32.to_uint idx{hr} * 2 ^ - JWord.W32.to_uint j{hr}))).
                                                             move => aux2.
                                                                   rewrite aux2.
                                                                   smt().
                                                                   rewrite JWord.W32.of_uintK.
                                                                   simplify.
                                                                   have := StdOrder.IntOrder.ler_weexpn2l 2 _ (- JWord.W32.to_uint j{hr}) 0 _.
                                                                   smt().

                                                                         smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                                                   BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
                                                             simplify.
                                                             move => aux3.
                                                             
                                                            
                                                                   have := IntDiv.modz_small (JWord.W32.to_uint idx{hr} * 2 ^ - JWord.W32.to_uint j{hr}) 4294967296.
                                                             move => temp4.
                                                             rewrite temp4.
                                                               
                                                          
                                                                                   smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                                                   BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).

                                                                   have : ((2 ^ (9 - JWord.W32.to_uint j{hr}) - 1)) = 511.
                                                             rewrite case0.

                                                                            smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                                                   BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
                                                                smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                                                   BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
                                                             move => case1.
                                                                   rewrite case0.
                                                                   simplify.
                                                                smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                                                   BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
                                                             move => case2.
                                                             
                                                                   have : 0 <= - JWord.W32.to_uint j{hr} = false.
                                                                   smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                                                   BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
                                                             move => aux.
                                                                   rewrite aux.
                                                                   simplify.

                                                                   have : 0 <= 9 - JWord.W32.to_uint j{hr} = true.

                                                                 smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                                                   BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
                                                             move => aux2.
                                                                   rewrite aux2.
                                                                   simplify.
                                                             move => aux3.
                                                             case : (((JWord.W32."_.[_]" ((JWord.W32.of_int (JWord.W32.to_uint idx{hr} %/ 2 ^ JWord.W32.to_uint j{hr}))) 0)) = true).
move => casse2.
have := lbt_xor_minus_one (JWord.W32.of_int
(JWord.W32.to_uint idx{hr} %/ 2 ^ JWord.W32.to_uint j{hr})).
move => aux4.
  rewrite aux4.
smt().
  rewrite JWord.W32.of_uintK.
  simplify.
have m8x : JWord.W32.to_uint (JWord.W32.of_int 9) = 9 by rewrite JWord.W32.of_uintK.
have hjj : JWord.W32.to_uint j{hr} <= 9 by smt(JWord.W32.uleE).
have hp8x : 2 ^ 9 = 512 by smt().
have hd : JWord.W32.to_uint idx{hr} %/ 2 ^ JWord.W32.to_uint j{hr} < 2 ^ (9 - JWord.W32.to_uint j{hr}).
  rewrite IntDiv.ltz_divLR 1:StdOrder.IntOrder.expr_gt0 //.
  rewrite -StdOrder.IntOrder.Domain.exprD_nneg; smt(JWord.W32.to_uint_cmp).
have hq : 0 < 2 ^ (9 - JWord.W32.to_uint j{hr}) by apply StdOrder.IntOrder.expr_gt0.
have hq2 : 2 ^ (9 - JWord.W32.to_uint j{hr}) <= 2 ^ 9 by apply StdOrder.IntOrder.ler_weexpn2l; smt(JWord.W32.to_uint_cmp).
smt(IntDiv.modz_small IntDiv.divz_ge0 StdOrder.IntOrder.expr_gt0 JWord.W32.to_uint_cmp).
move => casse2.

have := JWord.W32.splitwE 1 ((JWord.W32.(`^`)
     (JWord.W32.of_int
        (JWord.W32.to_uint idx{hr} %/ 2 ^ JWord.W32.to_uint j{hr}))
          JWord.W32.one)).
  move => aux4.
          rewrite aux4.
          smt().

  have := one_and_one_eq_one ((JWord.W32.(`^`)
        (JWord.W32.of_int
           (JWord.W32.to_uint idx{hr} %/ 2 ^ JWord.W32.to_uint j{hr}))
             JWord.W32.one)).
     move => aux5.
             rewrite aux5.

     have := xor_one_lbf ((JWord.W32.of_int
         (JWord.W32.to_uint idx{hr} %/ 2 ^ JWord.W32.to_uint j{hr}))).
     move => aux6.
           rewrite aux6.
           smt().
     smt().

         have := JWord.W32.to_uint_shr ((JWord.W32.(`^`)
        (JWord.W32.of_int
           (JWord.W32.to_uint idx{hr} %/ 2 ^ JWord.W32.to_uint j{hr}))
        JWord.W32.one)) 1.
       move => aux6.
       simplify.
             rewrite aux6.
             smt().
             simplify.

have := xor_one_lbf (JWord.W32.of_int
       (JWord.W32.to_uint idx{hr} %/ 2 ^ JWord.W32.to_uint j{hr})).
     move => aux7.
     have : Int.odd (JWord.W32.to_uint
   (JWord.W32.(`^`)
      (JWord.W32.of_int
         (JWord.W32.to_uint idx{hr} %/ 2 ^ JWord.W32.to_uint j{hr}))
           JWord.W32.one)).
           smt().
   move => aux8.

   have := div2_xor_eq ((JWord.W32.of_int
    (JWord.W32.to_uint idx{hr} %/ 2 ^ JWord.W32.to_uint j{hr}))).
move => aux9.
      rewrite -aux9.
      rewrite JWord.W32.of_uintK.

      case : (Int.odd (JWord.W32.to_uint idx{hr})).
move => cassse1.
      case : (2 <= JWord.W32.to_uint j{hr}).
move => casssse1.
      have := exp_div_split (JWord.W32.to_uint idx{hr}) (JWord.W32.to_uint j{hr}).
move => aux10.
      rewrite aux10.
      smt().
      have := odd_div2 (JWord.W32.to_uint idx{hr}).
move => aux11.
rewrite aux11.
smt().
simplify.
have m8y : JWord.W32.to_uint (JWord.W32.of_int 9) = 9 by rewrite JWord.W32.of_uintK.
have hjy : JWord.W32.to_uint j{hr} <= 9 by smt(JWord.W32.uleE).
have hj1y : 1 <= JWord.W32.to_uint j{hr} by smt(JWord.W32.to_uint_cmp).
have hqy : 0 < 2 ^ (9 - JWord.W32.to_uint j{hr}) by apply StdOrder.IntOrder.expr_gt0.
have hq2y : 2 ^ (9 - JWord.W32.to_uint j{hr}) <= 2 ^ 9 by apply StdOrder.IntOrder.ler_weexpn2l; smt(JWord.W32.to_uint_cmp).
have hp8y : 2 ^ 9 = 512 by smt().
have hs1y : 2 ^ (9 - JWord.W32.to_uint j{hr}) * 2 ^ (JWord.W32.to_uint j{hr} - 1) = 2 ^ (9 - 1).
  by rewrite -StdOrder.IntOrder.Domain.exprD_nneg 1,2:/#; congr; ring.
have hp7y : 2 ^ (9 - 1) * 2 = 2 ^ 9 by smt().
have hXy : (JWord.W32.to_uint idx{hr} - 1) %/ 2 %/ 2 ^ (JWord.W32.to_uint j{hr} - 1) < 2 ^ (9 - JWord.W32.to_uint j{hr}).
  rewrite IntDiv.ltz_divLR 1:StdOrder.IntOrder.expr_gt0 // hs1y IntDiv.ltz_divLR // hp7y; smt().
have hX0y : 0 <= (JWord.W32.to_uint idx{hr} - 1) %/ 2 %/ 2 ^ (JWord.W32.to_uint j{hr} - 1).
  apply IntDiv.divz_ge0; 1: smt(StdOrder.IntOrder.expr_gt0). apply IntDiv.divz_ge0 => //. smt(JWord.W32.to_uint_cmp).
have hq3y : 2 ^ (9 - JWord.W32.to_uint j{hr}) = 2 * 2 ^ (9 - JWord.W32.to_uint j{hr} - 1).
  rewrite -StdOrder.IntOrder.Domain.exprS; smt(JWord.W32.to_uint_cmp).
clear H4 H2 H5 H7 H8 temp temp0 xor_one_lbt xor_one_lbf xor_same_g0 one_and_one_eq_one zero_and_one_eq_zero shift_xor_eq shift_xor_eq_uint div2_xor_eq xor_one_bound lbt_odd lbf_nodd nodd_odd_tight_bound lbt_xor_minus_one.
smt(IntDiv.modz_small IntDiv.leq_trunc_div IntDiv.divz_ge0 IntDiv.ltz_divLR StdOrder.IntOrder.expr_gt0).
move => casssse2.

      have : (JWord.W32.to_uint j{hr}) = 1.
      smt().
move => aux10.
      rewrite aux10.
      simplify.
      have := odd_div2 (JWord.W32.to_uint idx{hr}).
move => aux11.
rewrite aux11.
      smt().

                                          smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
      BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
move => some_case.

      have := nodd_odd_tight_bound idx{hr} 511.
simplify.
move => aux10.
      have : JWord.W32.to_uint idx{hr} <= 510.
      smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one IntDiv.divzMDl IntDiv.oddW IntDiv.oddP).
move => aux11.

      have := IntDiv.modz_small (JWord.W32.to_uint idx{hr} %/ 2 ^ JWord.W32.to_uint j{hr}) 4294967296.
move => temp1.
rewrite temp1.
                                          smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
      BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).

have : 2 * (JWord.W32.to_uint idx{hr} %/ 2 ^ JWord.W32.to_uint j{hr} %/ 2) = ((JWord.W32.to_uint idx{hr} %/ 2 ^ JWord.W32.to_uint j{hr})).

                                          smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
      BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
move => aux12.
      rewrite aux12.

      have := StdOrder.IntOrder.ler_weexpn2l 2 _ (9 - JWord.W32.to_uint j{hr}) 8 _.
smt().



                smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
      BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
move => aux13.
      have := IntDiv.modz_small ((2 ^ (9 - JWord.W32.to_uint j{hr}) - 1)) 4294967296.
move => temp2.
      rewrite temp2.

                smt(xs_pow_le xs_pow_eq StdOrder.IntOrder.expr_gt0 JWord.W32.to_uint_cmp).
                have m8z : JWord.W32.to_uint (JWord.W32.of_int 9) = 9 by rewrite JWord.W32.of_uintK.
have hj8z : JWord.W32.to_uint j{hr} < 9 by smt(JWord.W32.ultE).
have hszz : 2 ^ (9 - JWord.W32.to_uint j{hr}) * 2 ^ JWord.W32.to_uint j{hr} = 2 ^ 9.
  have hj0z := JWord.W32.to_uint_cmp j{hr}.
  by rewrite -StdOrder.IntOrder.Domain.exprD_nneg 1,2:/#; congr; ring.
have hxz : JWord.W32.to_uint idx{hr} %/ 2 ^ JWord.W32.to_uint j{hr} < 2 ^ (9 - JWord.W32.to_uint j{hr}).
  rewrite IntDiv.ltz_divLR 1:StdOrder.IntOrder.expr_gt0 // hszz; smt(xs_pow_eq).
have hevz : 2 ^ (9 - JWord.W32.to_uint j{hr}) = 2 * 2 ^ (9 - JWord.W32.to_uint j{hr} - 1).
  rewrite -StdOrder.IntOrder.Domain.exprS; smt(JWord.W32.to_uint_cmp).
smt().

                smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
      BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).

      move : H6.
      rewrite /JWord.W32.(\ult).
      rewrite /JWord.W32.(\ule).
      rewrite /JWord.W32.(+).
rewrite /JWord.W32.ulift2.

                smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
      BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
      move : H2.
      rewrite /JWord.W64.(\ule).
      rewrite /JWord.W64.(+).
      rewrite /JWord.W64.ulift2.
      rewrite /JWord.W32.(+).
      rewrite /JWord.W32.ulift2.
      rewrite JWord.W64.of_uintK.
      rewrite JWord.W64.of_uintK.
      rewrite JWord.W64.of_uintK.
      rewrite JWord.W64.of_uintK.
      rewrite JWord.W32.of_uintK.
      rewrite JWord.W32.of_uintK.

                smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
      BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
      rewrite /JWord.W64.(\ule).
      rewrite /JWord.W64.(+).
      rewrite /JWord.W64.ulift2.
                smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
      BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).


  rewrite /JWord.W32.(`>>`).
have := shift_xor_eq ((JWord.W32.of_int
           (JUtils.(`|>>`) (JWord.W32.to_uint idx{hr})
             (JWord.W32.to_uint j{hr})))).
       move => aux.
               rewrite -aux.


         have :
         (JWord.W32.(`>>>`)
     (JWord.W32.of_int
        (JUtils.(`|>>`) (JWord.W32.to_uint idx{hr}) (JWord.W32.to_uint j{hr})))
     1)  =

  (JWord.W32.of_int
     (JUtils.(`|>>`) (JWord.W32.to_uint idx{hr})
       (JWord.W32.to_uint (JWord.W32.(+) j{hr} JWord.W32.one)))) =>
       (JWord.W32.(`^`)
  (JWord.W32.(`>>>`)
     (JWord.W32.of_int
        (JUtils.(`|>>`) (JWord.W32.to_uint idx{hr}) (JWord.W32.to_uint j{hr})))
     1) JWord.W32.one =
JWord.W32.(`^`)
  (JWord.W32.of_int
     (JUtils.(`|>>`) (JWord.W32.to_uint idx{hr})
        (JWord.W32.to_uint (JWord.W32.(+) j{hr} JWord.W32.one))))
          JWord.W32.one).

                     smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
          BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
  move => aux2.
  apply aux2.
  

         have :
         (JWord.W32.of_int(
         JWord.W32.to_uint(
(JWord.W32.(`>>>`)
  (JWord.W32.of_int
     (JUtils.(`|>>`) (JWord.W32.to_uint idx{hr}) (JWord.W32.to_uint j{hr}))))
  1)) =
JWord.W32.of_int
  (JUtils.(`|>>`) (JWord.W32.to_uint idx{hr})
     (JWord.W32.to_uint (JWord.W32.(+) j{hr} JWord.W32.one)))
) =>
JWord.W32.(`>>>`)
  (JWord.W32.of_int
     (JUtils.(`|>>`) (JWord.W32.to_uint idx{hr}) (JWord.W32.to_uint j{hr})))
  1 =
JWord.W32.of_int
  (JUtils.(`|>>`) (JWord.W32.to_uint idx{hr})
     (JWord.W32.to_uint (JWord.W32.(+) j{hr} JWord.W32.one))).


                  smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
      BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).

  move => aux3.

       apply aux3.

  have := JWord.W32.to_uint_shr ((JWord.W32.of_int
              (JUtils.(`|>>`) (JWord.W32.to_uint idx{hr})
                (JWord.W32.to_uint j{hr})))) 1.
          move => aux4.
                  rewrite aux4.
                  smt().
                  simplify.

            rewrite /JUtils.(`|>>`).
            rewrite /JUtils.(`<<`).

            case : (0 = JWord.W32.to_uint j{hr}).
          move => case1.

            have : 0 <= - JWord.W32.to_uint j{hr} = true.
          smt().

          move => aux5.
            rewrite aux5.
            simplify.

            have : 0 <= - JWord.W32.to_uint (JWord.W32.(+) j{hr} JWord.W32.one) = false.

            rewrite /JWord.W32.(+).
            rewrite /JWord.W32.ulift2.
          rewrite JWord.W32.of_uintK.
                            smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
            BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
          move => aux6.
            rewrite aux6.
            simplify.
          rewrite -case1.
            rewrite /JWord.W32.(+).
            rewrite /JWord.W32.ulift2.
            rewrite JWord.W32.of_uintK.
            simplify.
            rewrite JWord.W32.of_uintK.
          simplify.

            rewrite -case1.
            simplify.


            have := IntDiv.modz_small (JWord.W32.to_uint idx{hr} * 2 ^ - 0) 4294967296.
          move => aux7.
            rewrite aux7.
            simplify.
            move : H3.
            rewrite /JWord.W32.(\ule).
            rewrite /JUtils.(`<<`).
          simplify.
                                                                         smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
            BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
            smt().
          move => case2.

            have : 0 <= - JWord.W32.to_uint j{hr} = false.
          
          
                                                                         smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
            BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
          move => aux5.
            rewrite aux5.
            simplify.

            have : 0 <= - JWord.W32.to_uint (JWord.W32.(+) j{hr} JWord.W32.one) = false.
            rewrite /JWord.W32.(+).
          rewrite /JWord.W32.ulift2.

                                                                                   smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
            BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
          move => aux6.
            rewrite aux6.
            simplify.
            rewrite /JWord.W32.(+).
            rewrite /JWord.W32.ulift2.

            rewrite JWord.W32.of_uintK.
            rewrite JWord.W32.of_uintK.
            rewrite JWord.W32.of_uintK.
            simplify.

            have := StdOrder.IntOrder.ler_weexpn2l 2 _ (JWord.W32.to_uint j{hr}) 9 _.
          smt().

          

                                                                                             smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
            BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
          move => aux7.

          

            have := IntDiv.modz_small (JWord.W32.to_uint idx{hr} %/ 2 ^ JWord.W32.to_uint j{hr} ) 4294967296.
            move => temp.
            rewrite temp.
            move : H3.
            rewrite /JWord.W32.(\ule).
            rewrite /JUtils.(`<<`).
          simplify.

                                                                                                       smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
            BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).

            have := StdOrder.IntOrder.ler_weexpn2l 2 _ ((JWord.W32.to_uint j{hr} + 1)) 10 _.
            smt().
           smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
            BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
          move => aux8.

            have := IntDiv.modz_small ((JWord.W32.to_uint j{hr} + 1)) 4294967296.
          move => temp2.
            rewrite temp2.
                     smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
            BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).



            have := exp_div_split (JWord.W32.to_uint idx{hr}) ((JWord.W32.to_uint j{hr} + 1)).
          move => aux9.
            rewrite aux9.
            smt().
            simplify.

            have := IntDiv.divzMl (JWord.W32.to_uint idx{hr}) (2 ^ JWord.W32.to_uint j{hr}) 2.
          move => aux10.
            rewrite -aux10.

                   smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
            BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
            smt().


            have := IntDiv.divzMr (JWord.W32.to_uint idx{hr}) (2 ^ JWord.W32.to_uint j{hr}) 2.
          move => aux11.
            rewrite aux11.

                    smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
            BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
            smt().
            smt().

            rewrite SBArray1440_24.SBArray1440_24.is_init_cell_set.
            case : (JWord.W64.to_uint (JWord.W64.of_int (1224 + JWord.W32.to_uint j{hr} * 24)) <= i).
          move => case1.

          have : (i <
    24 +
    JWord.W64.to_uint
            (JWord.W64.of_int (1224 + JWord.W32.to_uint j{hr} * 24))) = true.

              move : H25.
              rewrite JWord.W64.of_uintK.
           rewrite JWord.W64.of_uintK.
                              smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
              BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
          move => cond_true.
              rewrite cond_true.
              simplify.

                      have : 0 <= i < 1440 = true.
            move : H25 H8.
            rewrite /JWord.W64.(+).
              rewrite /JWord.W64.ulift2.
                        smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
              BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
          move => aux.
              rewrite aux.
              simplify.
                       smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
              BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
              simplify.
                                smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
              BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
          rewrite JWord.W64.of_uintK.
                              smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
              BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
              rewrite /JWord.W32.(+).
          rewrite /JWord.W32.ulift2.
                              smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
              BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
            auto.
            progress.
            move : H4.
            rewrite /JUtils.(`<<`).
            simplify.
            trivial.
                                                smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
            BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
                                                smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
            BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).

            try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          have : 9 <= JWord.W32.to_uint j0.
            move : H11.
          rewrite /JWord.W32.(\ult).
                                                 smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
            BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
          move => aux.

              move : H17.
              rewrite JWord.W64.of_uintK.
              simplify.

                  have := IntDiv.modz_small ((1224 + JWord.W32.to_uint j0 * 24)) 18446744073709551616.

          move => temp.
          rewrite temp.
                                           smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
              BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
              simplify.
          move => aux2.
          have aux3 : JWord.W32.to_uint j0 = 9.
              smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
              BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
              move : aux2.
              rewrite aux3.
              simplify.
          move => aux4.

          rewrite /BArray1440.is_init.
move => k hk_lo hk_hi.
rewrite (SBArray1440_1224.SBArray1440_1224.is_init_cell_set b_sig_xmss0 
            (BArray1224.init_arr (JWord.W8.of_int 255)) 0 k).
              smt(BArray1224.init_arrP).

qed.
end section.



lemma __xmss_sign_proof _sig_xmss _b_sig_xmss _m _b_m _skseed _b_skseed _idx _pkseed _b_pkseed _adrs _b_adrs :
      (__xmss_sign_spec _sig_xmss _b_sig_xmss _m _b_m _skseed _b_skseed 
      _idx _pkseed _b_pkseed _adrs _b_adrs).
proof.
rewrite /__xmss_sign_spec .
proc; auto .
ecall (xmss_sign_proof param_4 b_param param_3 (BArray24.init_arr
                                               (JWord.W8.of_int 255)) param_2 
       (BArray24.init_arr (JWord.W8.of_int 255)) param_1 param_0 (BArray24.init_arr
                                                           (JWord.W8.of_int 255)) 
       param (BArray32.init_arr (JWord.W8.of_int 255))).
auto .
rewrite /JUtils.(`<<`).
smt(BArray32.init_arrP BArray24.init_arrP BArray1440.init_arrP).
qed .

lemma xmss_pkfromsig_proof _pk_xmss _b_pk_xmss _idx _sig_xmss _b_sig_xmss _m _b_m _pkseed _b_pkseed _adrs _b_adrs :
      (xmss_pkfromsig_spec _pk_xmss _b_pk_xmss _idx _sig_xmss _b_sig_xmss 
      _m _b_m _pkseed _b_pkseed _adrs _b_adrs).
proof.
rewrite /xmss_pkfromsig_spec .
proc; auto .
ecall (__copy_nbytes_proof param_36 b_param param_35 (BArray24.init_arr
                                                     (JWord.W8.of_int 255))).
auto .
while ((JWord.W32.(\ule) JWord.W32.zero k) /\
      (JWord.W32.(\ule) k (JWord.W32.of_int 9)) /\
      (JWord.W64.to_uint offset = 1224 + ((JWord.W32.to_uint k) * 24)) /\
      (BArray1440.is_init b_sig_xmss 0 1440)).
auto .

ecall (__copy_nbytes_proof param_34 (BArray24.init_arr (JWord.W8.of_int 255)) 
       param_33 (BArray24.init_arr (JWord.W8.of_int 255))).
auto .
ecall (__H_proof param_32 b_param_0 param_31 (BArray24.init_arr
                                             (JWord.W8.of_int 255)) param_30 
       (BArray32.init_arr (JWord.W8.of_int 255)) param_29 (BArray24.init_arr
                                                    (JWord.W8.of_int 255)) 
       param_28 (BArray24.init_arr (JWord.W8.of_int 255))).
auto .
sp.
seq 1 : (#pre /\ BArray32.is_init aux_0 0 32).

ecall (__adrs_set_tree_height_proof param_13 (BArray32.init_arr (JWord.W8.of_int 255)) param_12).
auto.
smt(BArray32.init_arrP BArray24.init_arrP).
sp.
if.
sp.
if.
auto.
ecall (__copy_nbytes_proof param_20 b_param_2 param_19 b_param_1).
auto .
ecall (__copy_nbytes_proof param_18 b_param_3 param_17 (BArray24.init_arr
                                                       (JWord.W8.of_int 255))).
auto .
ecall (__adrs_set_tree_index_proof param_16 (BArray32.init_arr
                                            (JWord.W8.of_int 255)) param_15).
auto .
ecall (__adrs_get_tree_index_proof param_14 (BArray32.init_arr
                                            (JWord.W8.of_int 255))).
auto .

progress; try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
smt(BArray32.init_arrP BArray24.init_arrP).
smt(JWord.W64.to_uint_cmp).
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
smt(SBArray1440_24.SBArray1440_24.is_init_cell_get).
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
rewrite /JWord.W64.(+).
rewrite /JWord.W64.ulift2.
rewrite /JWord.W32.(+).
rewrite /JWord.W32.ulift2.
rewrite JWord.W64.of_uintK.
rewrite JWord.W64.of_uintK.
rewrite JWord.W32.of_uintK.
rewrite JWord.W32.of_uintK.
smt(JWord.W32.to_uint_cmp).
                      

auto .
ecall (__copy_nbytes_proof param_27 b_param_4
       param_26 (BArray24.init_arr (JWord.W8.of_int 255))).
auto .

ecall (__copy_nbytes_proof param_25 b_param_6 param_24 b_param_5).
auto .
ecall (__adrs_set_tree_index_proof param_23 (BArray32.init_arr
                                            (JWord.W8.of_int 255)) param_22).
auto .
ecall (__adrs_get_tree_index_proof param_21 (BArray32.init_arr
                                            (JWord.W8.of_int 255))).
auto .

progress; try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
smt(BArray32.init_arrP BArray24.init_arrP).
smt(JWord.W32.to_uint_cmp).
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
smt(SBArray1440_24.SBArray1440_24.is_init_cell_get).
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
rewrite /JWord.W64.(+).
rewrite /JWord.W64.ulift2.
rewrite /JWord.W32.(+).
rewrite /JWord.W32.ulift2.
rewrite JWord.W64.of_uintK.
rewrite JWord.W64.of_uintK.
rewrite JWord.W32.of_uintK.
rewrite JWord.W32.of_uintK.
smt(JWord.W32.to_uint_cmp).
exfalso.
smt().

auto .
ecall (__adrs_set_tree_index_proof param_11 (BArray32.init_arr
                                            (JWord.W8.of_int 255)) param_10).
auto .
ecall (__adrs_set_type_and_clear_proof param_9 (BArray32.init_arr
                                               (JWord.W8.of_int 255)) param_8).
auto .
ecall (__wots_pkfromsig_proof param_7 b_param_8 param_6 b_param_7 param_5 
       (BArray24.init_arr (JWord.W8.of_int 255)) param_4 (BArray24.init_arr
                                                   (JWord.W8.of_int 255)) param_3 
       (BArray32.init_arr (JWord.W8.of_int 255))).
auto .
ecall (__adrs_set_key_pair_addr_proof param_2 (BArray32.init_arr
                                              (JWord.W8.of_int 255)) param_1).
auto .
ecall (__adrs_set_type_and_clear_proof param_0 (BArray32.init_arr
                                               (JWord.W8.of_int 255)) param).
auto .
smt(SBArray1440_1224.SBArray1440_1224.is_init_cell_get BArray32.init_arrP BArray24.init_arrP).
qed .

lemma __xmss_pkfromsig_proof _pk_xmss _b_pk_xmss _idx _sig_xmss _b_sig_xmss _m _b_m _pkseed _b_pkseed _adrs _b_adrs :
      (__xmss_pkfromsig_spec _pk_xmss _b_pk_xmss _idx _sig_xmss _b_sig_xmss
      _m _b_m _pkseed _b_pkseed _adrs _b_adrs).
proof.
rewrite /__xmss_pkfromsig_spec .
proc; auto .
ecall (xmss_pkfromsig_proof param_4 b_param param_3 param_2 (
                                                            BArray1440.init_arr
                                                            (JWord.W8.of_int 255)) 
       param_1 (BArray24.init_arr (JWord.W8.of_int 255)) param_0 (BArray24.init_arr
                                                           (JWord.W8.of_int 255)) 
       param (BArray32.init_arr (JWord.W8.of_int 255))).
auto .
smt(BArray1440.init_arrP BArray32.init_arrP BArray24.init_arrP).
qed .

lemma __ht_update_idx_proof _idx_leaf _idx_tree _b_idx_tree :
      (__ht_update_idx_spec _idx_leaf _idx_tree _b_idx_tree).
proof.
rewrite /__ht_update_idx_spec .
proc; auto .
progress.
smt(BArray12.init_arrP).
rewrite /JUtils.(`<<`).
rewrite /JWord.W32.(\ule).
rewrite (JWord.W32.to_uint_and_mod 9 ((BArray12.get32d idx_tree{hr} 8))).
trivial.
smt().
qed .

lemma ht_sign_proof _sig_ht _b_sig_ht _pk_fors _b_pk_fors _skseed _b_skseed _pkseed _b_pkseed _tree _b_tree _leaf :
      (ht_sign_spec _sig_ht _b_sig_ht _pk_fors _b_pk_fors _skseed _b_skseed
      _pkseed _b_pkseed _tree _b_tree _leaf).
      proof.
rewrite /ht_sign_spec .
proc; auto .
while (JWord.W32.(\ule) JWord.W32.one j /\
      (JWord.W32.(\ule) j (JWord.W32.of_int 7)) /\
      (JWord.W64.(\ule) (JWord.W64.of_int 1440) offset) /\
      (JWord.W64.(\ule) offset (JWord.W64.of_int 10080)) /\
      (JWord.W64.to_uint offset = (JWord.W32.to_uint j) * 1440) /\
      (BArray10080.is_init b_sig_ht 0 (JWord.W64.to_uint offset)) /\
      (BArray12.is_init b_idx_tree 0 12)).
    
        auto .
sp.
        seq 1 : (#pre /\ JWord.W32.to_uint aux_5 <= 511 /\ BArray12.is_init aux_7 0 12).
      ecall (__ht_update_idx_proof param_15 param_14 b_param_1).
auto.
progress.
move : H9.
rewrite /JUtils.(`<<`).
simplify.
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
sp.
if.
        sp.
seq 1 : (#pre /\ BArray32.is_init aux_0 0 32).
ecall (__adrs_set_layer_addr_proof param_17 (BArray32.init_arr (JWord.W8.of_int 255)) param_16).
        auto.
        smt(BArray32.init_arrP BArray24.init_arrP).
        sp.
        if.
        sp.
    wp.
        seq 1 : ((exists (adrs0 : BArray32.t),
    adrs = result_7 /\
    param_19 = adrs /\
    param_18 = idx_tree /\
    ((*result_7 = aux /\
     b_result_5 = aux_0 /\*)
     (exists (idx_tree0 b_idx_tree0 : BArray12.t) (idx_leaf0 : JWord.W32.t),
        idx_leaf = result_6 /\
        b_idx_tree = BArray12.init_arr (JWord.W8.of_int 255) /\
        idx_tree = result_5 /\
        param_17 = adrs0 /\
        param_16 = j /\
        (result_6 = aux_5 /\
         result_5 = aux_6 /\
         b_result_6 = aux_7 /\
         (param_15 = idx_leaf0 /\
          b_param_1 = b_idx_tree0 /\
          param_14 = idx_tree0 /\
          (JWord.W32.(\ule) JWord.W32.one j /\
           JWord.W32.(\ule) j (JWord.W32.of_int 7) /\
           JWord.W64.(\ule) (JWord.W64.of_int 1440) offset /\
           JWord.W64.(\ule) offset (JWord.W64.of_int 10080) /\
           JWord.W64.to_uint offset = JWord.W32.to_uint j * 1440 /\
           BArray10080.is_init b_sig_ht 0 (JWord.W64.to_uint offset) /\
           BArray12.is_init b_idx_tree0 0 12 (*/\ BArray32.is_init b_adrs 0 32*)) /\
          JWord.W32.(\ult) j (JWord.W32.of_int 7)) /\
         JWord.W32.to_uint aux_5 <= 511 /\ BArray12.is_init aux_7 0 12) /\
        BArray12.is_init b_result_6 0 12 /\
        JWord.W32.(\ule) result_6 (JWord.W32.of_int 511)) /\
     BArray32.is_init aux_0 0 32) /\
    BArray32.is_init b_result_5 0 32) /\ (BArray32.is_init aux_0 0 32)).
ecall (__adrs_set_tree_addr_proof param_19 (BArray32.init_arr (JWord.W8.of_int 255)) param_18
          (BArray12.init_arr (JWord.W8.of_int 255))).
            auto.

        smt(BArray12.init_arrP BArray32.init_arrP BArray24.init_arrP).
        sp.
        
            if .
            sp.
            seq 1 : (#pre /\ BArray24.is_init b_result_3 0 24).
            ecall (__copy_nbytes_proof param_21 b_param_0 param_20 (BArray24.init_arr (JWord.W8.of_int 255))).
            auto.
            smt(BArray32.init_arrP BArray24.init_arrP).
            if.
            sp.
            if.
            sp.
        seq 1 : ((b_sig_xmss =
  SBArray10080_1440.SBArray10080_1440.get_sub b_sig_ht
    (JWord.W64.to_uint offset) /\
  sig_xmss =
  SBArray10080_1440.SBArray10080_1440.get_sub sig_ht
    (JWord.W64.to_uint offset) /\
  b_param = b_sig_xmss /\
  param_27 = sig_xmss /\
  param_26 = root_prev /\
  param_25 = skseed /\
  param_24 = idx_leaf /\
  param_23 = pkseed /\
  param_22 = adrs /\
  (exists (root_prev0 b_root_prev0 : BArray24.t),
     b_root_prev = BArray24.init_arr (JWord.W8.of_int 255) /\
     root_prev = result_9 /\
     ((exists (adrs0 : BArray32.t),
         adrs = result_8 /\
         b_param_0 = b_root_prev0 /\
         param_21 = root_prev0 /\
         param_20 = root /\
         ((*result_8 = aux /\
          b_result_4 = aux_0 /\*)
          (exists (adrs0_0 : BArray32.t),
             adrs0 = result_7 /\
             param_19 = adrs0 /\
             param_18 = idx_tree /\
             ((exists (idx_tree0 b_idx_tree0 : BArray12.t)
                 (idx_leaf0 : JWord.W32.t),
                 idx_leaf = result_6 /\
                 b_idx_tree = BArray12.init_arr (JWord.W8.of_int 255) /\
                 idx_tree = result_5 /\
                 param_17 = adrs0_0 /\
                 param_16 = j /\
                 (result_6 = aux_5 /\
                  result_5 = aux_6 /\
                  b_result_6 = aux_7 /\
                  (param_15 = idx_leaf0 /\
                   b_param_1 = b_idx_tree0 /\
                   param_14 = idx_tree0 /\
                   (JWord.W32.(\ule) JWord.W32.one j /\
                    JWord.W32.(\ule) j (JWord.W32.of_int 7) /\
                    JWord.W64.(\ule) (JWord.W64.of_int 1440) offset /\
                    JWord.W64.(\ule) offset (JWord.W64.of_int 10080) /\
                    JWord.W64.to_uint offset = JWord.W32.to_uint j * 1440 /\
                    BArray10080.is_init b_sig_ht 0 (JWord.W64.to_uint offset) /\
                    BArray12.is_init b_idx_tree0 0 12 (*/\
                    BArray32.is_init b_adrs 0 32*)) /\
                   JWord.W32.(\ult) j (JWord.W32.of_int 7)) /\
                  JWord.W32.to_uint aux_5 <= 511 /\
                  BArray12.is_init aux_7 0 12) /\
                 BArray12.is_init b_result_6 0 12 /\
                 JWord.W32.(\ule) result_6 (JWord.W32.of_int 511)) /\
              BArray32.is_init aux_0 0 32) /\
             BArray32.is_init b_result_5 0 32) /\
          BArray32.is_init aux_0 0 32) /\
         BArray32.is_init b_result_4 0 32) /\
      BArray24.is_init b_result_3 0 24) /\
     BArray24.is_init b_result_3 0 24) /\
                     0 <= JWord.W64.to_uint offset /\ JWord.W64.to_uint offset + 1440 <= 10080) /\ BArray1440.is_init aux_2 0 1440 /\ BArray32.is_init aux_0 0 32).

ecall (__xmss_sign_proof param_27 b_param param_26 (BArray24.init_arr (JWord.W8.of_int 255)) param_25       (BArray24.init_arr (JWord.W8.of_int 255)) param_24 param_23
      (BArray24.init_arr (JWord.W8.of_int 255)) param_22
      (BArray32.init_arr (JWord.W8.of_int 255))).
        auto.
        progress.
        smt(BArray32.init_arrP BArray24.init_arrP).
        smt(BArray32.init_arrP BArray24.init_arrP).
        smt(BArray32.init_arrP BArray24.init_arrP).
        smt(BArray32.init_arrP BArray24.init_arrP).
        smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
    rewrite /JUtils.(`<<`).
        smt().
        smt().
    sp.
        if.
        sp.
        if.
        sp.
        if.
    auto.

ecall (__xmss_pkfromsig_proof param_33 (BArray24.init_arr (JWord.W8.of_int 255)) 
       param_32 param_31 (BArray1440.init_arr (JWord.W8.of_int 255)) param_30 
       (BArray24.init_arr (JWord.W8.of_int 255)) param_29 (BArray24.init_arr
                                                    (JWord.W8.of_int 255)) 
       param_28 (BArray32.init_arr (JWord.W8.of_int 255))).
                                                      auto .
                                                      progress.
                                                      smt(BArray1440.init_arrP).
                                                      smt(BArray32.init_arrP BArray24.init_arrP).
                                                      smt(BArray32.init_arrP BArray24.init_arrP).
                                                      smt(BArray32.init_arrP BArray24.init_arrP).
                                                      smt(JWord.W32.to_uint_cmp JWord.W32.to_uint_small).
                                                      smt( JWord.W32.of_uintK JWord.W32.to_uint_cmp).
                                                      rewrite /JWord.W64.(+).
                                                      rewrite /JWord.W64.ulift2.
                                                      rewrite JWord.W64.of_uintK.
                                                      rewrite /JWord.W64.(\ule).
                                                      rewrite JWord.W64.of_uintK.
                                                rewrite JWord.W64.of_uintK.
                                                      smt().
                                                      rewrite /JWord.W64.(+).
                                                      rewrite /JWord.W64.ulift2.
                                                      rewrite JWord.W64.of_uintK.
                                                      rewrite /JWord.W64.(\ule).
                                                rewrite JWord.W64.of_uintK.
                                                      smt().
                                                      rewrite /JWord.W64.(+).
                                                      rewrite /JWord.W64.ulift2.
                                                      rewrite /JWord.W32.(+).
                                                      rewrite /JWord.W32.ulift2.
                                                      rewrite JWord.W64.of_uintK.
                                                      rewrite JWord.W64.of_uintK.
                                                      rewrite JWord.W32.of_uintK.
                                                      rewrite JWord.W32.of_uintK.
                                                      smt().
                                                      rewrite /BArray10080.is_init.
                                                move => a b c.
                                                      rewrite (SBArray10080_1440.SBArray10080_1440.is_init_cell_set b_sig_ht0 (BArray1440.init_arr (JWord.W8.of_int 255)) (JWord.W64.to_uint offset{hr}) a).
                                                      smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
                                                      smt(BArray12.init_arrP).
                                                      auto.
                                                      progress.
                                                      smt(JWord.W32.to_uint_cmp JWord.W32.to_uint_small).
                                                      smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
                                                      rewrite /JWord.W64.(+).
                                                      rewrite /JWord.W64.ulift2.
                                                      rewrite /JWord.W64.(\ule).
                                                      rewrite JWord.W64.of_uintK.
                                                      rewrite JWord.W64.of_uintK.
                                                      smt().
                                                      rewrite /JWord.W64.(+).
                                                      rewrite /JWord.W64.ulift2.
                                                      rewrite /JWord.W64.(\ule).
                                                      rewrite JWord.W64.of_uintK.
                                                      rewrite JWord.W64.of_uintK.
                                                      rewrite JWord.W64.of_uintK.
                                                      smt().
                                                      rewrite /JWord.W64.(+).
                                                      rewrite /JWord.W64.ulift2.
                                                      rewrite /JWord.W32.(+).
                                                      rewrite /JWord.W32.ulift2.
                                                      rewrite JWord.W64.of_uintK.
                                                      rewrite JWord.W64.of_uintK.
                                                      rewrite JWord.W32.of_uintK.
                                                      rewrite JWord.W32.of_uintK.
                                                      smt().

                                                      rewrite /BArray10080.is_init.
                                                move => a b c.
                                                      rewrite (SBArray10080_1440.SBArray10080_1440.is_init_cell_set b_sig_ht0 (BArray1440.init_arr (JWord.W8.of_int 255)) (JWord.W64.to_uint offset{hr}) a).
                                                case : (JWord.W64.to_uint offset{hr} <= a).

                                                      have : ((true && a < 1440 + JWord.W64.to_uint offset{hr}) /\ 0 <= a < 10080) = true.

                                                      smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp ).

                                                      smt(BArray1440.init_arrP).
                                                      smt().
                                                      smt(BArray12.init_arrP).
                                                      exfalso.
                                                      smt().
                                                      exfalso.
                                                      smt().
                                                      exfalso.
                                                      smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
                                                      exfalso.
                                                      smt().
                                                      exfalso.
                                                      smt().
                                                      exfalso.
                                                      smt().
                                                      exfalso.
                                                move => &hr.
                                                move => *.
                                                      have : (BArray12.is_init b_result_6{hr} 0 12).
                                                      smt().
                                                move => part1.
                                                      have : (JWord.W32.(\ule) result_6{hr} (JWord.W32.of_int 511)).
                                                rewrite /JWord.W32.(\ule).

                                                      smt().
                                                      smt().

                                                auto.
                                                
                                                
ecall (__xmss_pkfromsig_proof param_13 b_param_2 param_12 param_11 (
                                                                   BArray1440.init_arr
                                                                   (JWord.W8.of_int
                                                                   255)) 
       param_10 (BArray24.init_arr (JWord.W8.of_int 255)) param_9 (
                                                            BArray24.init_arr
                                                            (JWord.W8.of_int 255)) 
       param_8 (BArray32.init_arr (JWord.W8.of_int 255))).
auto .
ecall (__xmss_sign_proof param_7 b_param_3 param_6 (BArray24.init_arr
                                                   (JWord.W8.of_int 255)) param_5 
       (BArray24.init_arr (JWord.W8.of_int 255)) param_4 param_3 (BArray24.init_arr
                                                           (JWord.W8.of_int 255)) 
       param_2 (BArray32.init_arr (JWord.W8.of_int 255))).
auto .
ecall (__adrs_set_tree_addr_proof param_1 (BArray32.init_arr (JWord.W8.of_int 255)) 
       param_0 b_param_4).
                                                             auto .
                                                       sp.
                                                        ecall (__adrs_init_proof param b_param_5).
                                                             auto .
while (0 <= i /\ i <= 3 /\ BArray12.is_init b_idx_tree 0 (4 * i)).
                                                             auto .
                                                         smt(BArray12.is_init_cell_set32d).
                                                       wp.
                                                             auto.

progress; try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
                                                             move : H4.
                                                             rewrite /JUtils.(`<<`).
                                                             smt().
                                                             smt(BArray12.init_arrP).
                                                             smt().
                                                             smt(BArray32.init_arrP BArray24.init_arrP).
                                                             smt(BArray1440.init_arrP).
                                                         smt(SBArray10080_1440.SBArray10080_1440.is_init_cell_set).
                                                         have : (JWord.W64.to_uint offset0) = 10080.
                                                         move : H47.
                                                       rewrite /JWord.W32.(\ult).
                                                         smt( JWord.W32.of_uintK JWord.W32.to_uint_cmp).
                                                       smt().
qed .

lemma __ht_sign_proof _sig_ht _b_sig_ht _pk_fors _b_pk_fors _skseed _b_skseed _pkseed _b_pkseed _tree _b_tree _leaf :
      (__ht_sign_spec _sig_ht _b_sig_ht _pk_fors _b_pk_fors _skseed _b_skseed
      _pkseed _b_pkseed _tree _b_tree _leaf).
proof.
rewrite /__ht_sign_spec .
proc; auto .
ecall (ht_sign_proof param_4 b_param param_3 (BArray24.init_arr
                                             (JWord.W8.of_int 255)) param_2 
       (BArray24.init_arr (JWord.W8.of_int 255)) param_1 (BArray24.init_arr
                                                   (JWord.W8.of_int 255)) param_0 
       (BArray12.init_arr (JWord.W8.of_int 255)) param).
auto .
rewrite /JUtils.(`<<`).
smt(BArray12.init_arrP BArray32.init_arrP BArray24.init_arrP BArray10080.init_arrP).
qed .

lemma ht_verify_proof _pk_fors _b_pk_fors _sig_ht _b_sig_ht _pkseed _b_pkseed _tree _b_tree _leaf _pkroot _b_pkroot :
      (ht_verify_spec _pk_fors _b_pk_fors _sig_ht _b_sig_ht _pkseed _b_pkseed
      _tree _b_tree _leaf _pkroot _b_pkroot).
proof.
rewrite /ht_verify_spec .
proc; auto .
ecall (__memcmp_proof param_23 (BArray24.init_arr (JWord.W8.of_int 255)) param_22 
       (BArray24.init_arr (JWord.W8.of_int 255))).
auto .
while (JWord.W32.(\ule) JWord.W32.one j /\
      (JWord.W32.(\ule) j (JWord.W32.of_int 7)) /\
      (JWord.W64.(\ule) (JWord.W64.of_int 1440) offset) /\
      (JWord.W64.(\ule) offset (JWord.W64.of_int 10080)) /\
      (JWord.W64.to_uint offset = (JWord.W32.to_uint j) * 1440) /\
      (BArray12.is_init b_idx_tree 0 12) /\
      (BArray10080.is_init b_sig_ht 0 10080)).
auto .
ecall (__xmss_pkfromsig_proof param_21 (BArray24.init_arr (JWord.W8.of_int 255)) 
       param_20 param_19 b_param param_18 (BArray24.init_arr (JWord.W8.of_int 255)) 
       param_17 (BArray24.init_arr (JWord.W8.of_int 255)) param_16 (
                                                             BArray32.init_arr
                                                             (JWord.W8.of_int 255))).
auto .
ecall (__copy_nbytes_proof param_15 b_param_0 param_14 (BArray24.init_arr
                                                       (JWord.W8.of_int 255))).
auto .
ecall (__adrs_set_tree_addr_proof param_13 (BArray32.init_arr (JWord.W8.of_int 255)
                                           ) param_12 (BArray12.init_arr
                                                      (JWord.W8.of_int 255))).
auto .
ecall (__adrs_set_layer_addr_proof param_11 (BArray32.init_arr
                                            (JWord.W8.of_int 255)) param_10).
auto .
ecall (__ht_update_idx_proof param_9 param_8 b_param_1).
auto .
                                        
rewrite /is_init.

progress; try (apply (BArray24.init_arrP witness)).
move : H8.
rewrite /JUtils.(`<<`).
simplify.
trivial.
smt(BArray32.init_arrP BArray24.init_arrP).
smt(BArray12.init_arrP).
smt(JWord.W64.to_uint_cmp).
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
rewrite SBArray10080_1440.SBArray10080_1440.is_init_cell_get.
smt().
smt().
smt().
rewrite /JWord.W32.(+).
rewrite /JWord.W32.ulift2.
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
rewrite /JWord.W32.(+).
rewrite /JWord.W32.ulift2.
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
move : H1.
rewrite /JWord.W64.(+).
rewrite /JWord.W64.ulift2.
rewrite /JWord.W64.(\ule).
rewrite JWord.W64.of_uintK.
rewrite JWord.W64.of_uintK.
smt().
rewrite /JWord.W64.(+).
rewrite /JWord.W64.ulift2.
rewrite JWord.W64.of_uintK.
rewrite /JWord.W64.(\ule).
rewrite JWord.W64.of_uintK.
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
rewrite /JWord.W64.(+).
rewrite /JWord.W64.ulift2.
rewrite /JWord.W32.(+).
rewrite /JWord.W32.ulift2.
rewrite JWord.W64.of_uintK.
rewrite JWord.W64.of_uintK.
rewrite JWord.W32.of_uintK.
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).

auto .
ecall (__xmss_pkfromsig_proof param_7 b_param_3 param_6 param_5 b_param_2 
       param_4 (BArray24.init_arr (JWord.W8.of_int 255)) param_3 (BArray24.init_arr
                                                           (JWord.W8.of_int 255)) 
       param_2 (BArray32.init_arr (JWord.W8.of_int 255))).
auto .
ecall (__adrs_set_tree_addr_proof param_1 (BArray32.init_arr (JWord.W8.of_int 255)) 
       param_0 b_param_4).
auto .
ecall (__adrs_init_proof param b_param_5).
auto .
while (0 <= i /\ i <= 3 /\
       BArray12.is_init b_idx_tree 0 (4 * i)).
auto .    
smt(BArray12.is_init_cell_set32d).
auto.

progress; try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
smt().
smt().
smt(BArray32.init_arrP BArray24.init_arrP).
rewrite /BArray1440.is_init.
move => k l t.
rewrite (SBArray10080_1440.SBArray10080_1440.is_init_cell_get b_sig_ht{hr} k 0).
smt().
smt().
smt().
qed .

lemma __ht_verify_proof _pk_fors _b_pk_fors _sig_ht _b_sig_ht _pkseed _b_pkseed _tree _b_tree _leaf _pkroot _b_pkroot :
      (__ht_verify_spec _pk_fors _b_pk_fors _sig_ht _b_sig_ht _pkseed
      _b_pkseed _tree _b_tree _leaf _pkroot _b_pkroot).
proof.
rewrite /__ht_verify_spec .
proc; auto .
ecall (ht_verify_proof param_4 (BArray24.init_arr (JWord.W8.of_int 255)) param_3 
       (BArray10080.init_arr (JWord.W8.of_int 255)) param_2 (BArray24.init_arr
                                                      (JWord.W8.of_int 255)) 
       param_1 (BArray12.init_arr (JWord.W8.of_int 255)) param_0 param (
                                                                 BArray24.init_arr
                                                                 (JWord.W8.of_int
                                                                 255))).
auto .
smt(BArray12.init_arrP BArray32.init_arrP BArray24.init_arrP BArray10080.init_arrP).
qed .

lemma baseb_fors____base_b_proof _baseb _b_baseb _input _b_input :
    (baseb_fors____base_b_spec _baseb _b_baseb _input _b_input).
    proof.
rewrite /baseb_wots_m____base_b_spec .
      proc; auto .
while (0 <= out /\ out <= 17 /\
      ((1 <= out) => (BArray68.is_init b_baseb 0 (out * 4))) /\
      (0 <= JWord.W32.to_uint bits) /\ ((JWord.W32.to_uint bits) < 8) /\
      (0 <= JWord.W64.to_uint in_0) /\ ((JWord.W64.to_uint in_0) <= 30) /\
      (8 * JWord.W64.to_uint in_0 = 14 * out + JWord.W32.to_uint bits) /\
      (forall (k : int),
       (0 <= k /\ k < out) =>
       JWord.W32.to_uint (BArray68.get32d baseb (4 * k)) < 16384)).
auto.
while ((0 <= JWord.W32.to_uint bits) /\ ((JWord.W32.to_uint bits) <= 21) /\
      (0 <= JWord.W64.to_uint in_0) /\ ((JWord.W64.to_uint in_0) <= 30) /\
      (8 * JWord.W64.to_uint in_0 = 14 * out + JWord.W32.to_uint bits) /\
      (out < 17)).
        auto.
    progress; first 5
        smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).

        rewrite /JWord.W64.(+).
        rewrite /JWord.W64.ulift2.
        rewrite /JWord.W32.(+).
        rewrite /JWord.W32.ulift2.
        rewrite JWord.W64.of_uintK.
        rewrite JWord.W64.of_uintK.
        rewrite JWord.W32.of_uintK.
        rewrite JWord.W32.of_uintK.
         smt().
    
        auto.
        progress; first 7
        smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp BArray68.init_arrP BArray68.is_init_cell_set32d).
        move: H8.
        rewrite /JWord.W32.(\ult) /JWord.W32.(\ule) /JWord.W32.(+) /JWord.W32.ulift2 /JWord.W32.([-]) /JWord.W32.ulift1 !JWord.W32.of_uintK.
        move: H9.
        move: H11.
        rewrite /JWord.W32.(\ult).
        rewrite JWord.W32.of_uintK.
        smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
        move: H14.
        rewrite /JWord.W32.(\ult) /JWord.W32.(+) /JWord.W32.([-]) !JWord.W32.of_uintK.
        have : (((JWord.W32.to_uint bits0) + 4294967282) %% 4294967296) = JWord.W32.to_uint bits0 - 14.
        move: H9.
        move: H11.
        rewrite /JWord.W32.(\ult).
        rewrite JWord.W32.of_uintK.
        smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
    move => temp.
    move => aux.
        smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
        rewrite /JWord.W32.(\ult).
        have : (forall (w : JWord.W64.t), (JWord.W64.(\ult) (JWord.W64.(`&`) w (JWord.W64.of_int 16383))
        (JWord.W64.of_int 16384))).
      rewrite /JWord.W64.(\ult).
      rewrite JWord.W64.of_uintK.
      have : 16383 = (2^14)-1.
    smt().
    move: JWord.W64.to_uint_and_mod.
    move => hkeq h15eq w.
    have aux := hkeq 14 w _.
    smt().
    smt().
    move => less_than_512_after_mask.
    case : (k < out{hr}).
    smt(BArray68.get_set32dE).
    smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp BArray68.get_set32E_eq).
    auto.
          rewrite /JWord.W32.(\ult).
    progress.
          smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
          rewrite and_iota.
          smt().
          smt().
          rewrite and_iota.
          rewrite /JUtils.(`<<`).
    smt().
qed .

lemma __forest_label_proof _i _z : (__forest_label_spec _i _z).
proof.
    
rewrite /__forest_label_spec .
      proc; auto .
      progress.
      rewrite /JWord.W64.(`>>`).
      rewrite JWord.W64.to_uint_shr.
      smt().
      simplify.
      rewrite /JWord.W64.SHIFT.SHL_64.
      simplify.
      rewrite /JWord.W64.SHIFT.rflags_OF.
      simplify.
      rewrite /JWord.W64.ALU.SF_of.
      simplify.
      rewrite /JWord.W64.ALU.ZF_of.
      rewrite /JWord.W64.shift_mask.
      simplify.
    rewrite /JWord.W4u8.truncateu8.
    have : (JWord.W8.to_uint
        (JWord.W8.of_int
           (JWord.W32.to_uint
              (JWord.W32.WRingA.(-) (JWord.W32.of_int 15) z{hr}))) %%
          64 = 0) = false.
                rewrite JWord.W8.of_uintK.
                rewrite /JWord.W32.(+).
                rewrite /JWord.W32.ulift2.
                rewrite JWord.W32.of_uintK.
                rewrite JWord.W32.of_uintK.
                rewrite /JWord.W32.([-]).
        rewrite /JWord.W32.ulift1.
                simplify.
        rewrite JWord.W32.of_uintK.
                smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
        move => temp.
                rewrite temp.
                simplify.
          rewrite JWord.W64.to_uint_shl.
          smt().
          rewrite /JWord.W32.(+).
          rewrite /JWord.W32.ulift2.
          rewrite /JWord.W32.([-]).
          rewrite /JWord.W32.ulift1.
          rewrite JWord.W32.of_uintK.
          rewrite JWord.W32.of_uintK.
          rewrite JWord.W32.of_uintK.
          simplify.
          have : ((15 + (- JWord.W32.to_uint z{hr}) %% 4294967296) %% 4294967296) = ((15 + (- JWord.W32.to_uint z{hr})) %% 4294967296).
          smt().
        move => temp2.
          rewrite temp2.
          have : ((15 - JWord.W32.to_uint z{hr})) <= 15.
          smt(JWord.W32.to_uint_cmp).
        move => temp3.
          have : 1 <= ((15 - JWord.W32.to_uint z{hr})).
                                  smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
          have : (((15 - JWord.W32.to_uint z{hr}) %% 4294967296 %% 256 %% 64)) = (((15 - JWord.W32.to_uint z{hr}))).
          smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
        move => temp4.
          rewrite temp4.
        move => aux.

          have : (2 ^ (15 - JWord.W32.to_uint z{hr})) <= 32768.
          have := StdOrder.IntOrder.ler_weexpn2l 2 _ ((15 - JWord.W32.to_uint z{hr})) 15 _.
          trivial.
          smt().
        smt().
          smt(StdOrder.IntOrder.ler_weexpn2l StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS).
          rewrite /JUtils.(`<<`).
        have: (0 <=
         JWord.W32.to_uint (JWord.W32.WRingA.(-) (JWord.W32.of_int 14) z{hr})) = true.
          smt(JWord.W32.to_uint_cmp).
      
        move => cond_true.
          rewrite cond_true.
          simplify.
          rewrite /JWord.W32.(+).
          rewrite /JWord.W32.ulift2.
          rewrite /JWord.W32.([-]).
          rewrite /JWord.W32.ulift1.
          rewrite JWord.W32.of_uintK.
          rewrite JWord.W32.of_uintK.
          rewrite JWord.W32.of_uintK.
          rewrite JWord.W32.of_uintK.
          simplify.
        have : ((14 + (- JWord.W32.to_uint z{hr}) %% 4294967296) %% 4294967296) = ((14 + (- JWord.W32.to_uint z{hr}))).
         smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
        move => temp.
          rewrite temp.
          have := StdOrder.IntOrder.ler_weexpn2l 2 _ (14 - JWord.W32.to_uint z{hr}) 14 _.
        trivial.
        smt(JWord.W32.to_uint_cmp).
          smt(StdOrder.IntOrder.expr_gt0).


          rewrite /JWord.W64.SHIFT.SHL_64.
          simplify.
          rewrite /JWord.W64.SHIFT.rflags_OF.
          simplify.
          rewrite /JWord.W64.ALU.SF_of.
          simplify.
          rewrite /JWord.W64.ALU.ZF_of.
          simplify.
          rewrite /JWord.W64.shift_mask.
          simplify.
        rewrite /JWord.W4u8.truncateu8.
        have : (JWord.W8.to_uint
              (JWord.W8.of_int (JWord.W32.to_uint (JWord.W32.of_int 15))) %%
            64 = 0) = false.
                smt().
            move => temp.
                rewrite temp.
                simplify.
            have : (JWord.W32.to_uint
              (JWord.W32.WRingA.(-) (JWord.W32.of_int 15) z{hr}) %%
                256 %% 64 = 0) = false.

                rewrite /JWord.W32.(+).
                rewrite /JWord.W32.ulift2.
                rewrite /JWord.W32.([-]).
                rewrite /JWord.W32.ulift1.
                rewrite JWord.W32.of_uintK.
                rewrite JWord.W32.of_uintK.
            rewrite JWord.W32.of_uintK.
                smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
            move => temp2.
                rewrite temp2.
                simplify.
                rewrite /JWord.W64.(`>>`).
                rewrite /JWord.W64.(\ule).
                rewrite /JWord.W64.(+).
                rewrite /JWord.W64.ulift2.
                rewrite /JWord.W64.(+).
                rewrite /JWord.W64.ulift2.
                rewrite /JWord.W64.([-]).
            rewrite /JWord.W64.ulift1.
                rewrite JWord.W64.to_uint_shl.
                trivial.
                rewrite JWord.W64.to_uint_shl.
                smt().
                rewrite /JWord.W2u32.zeroextu64.
                rewrite JWord.W64.of_uintK.
                rewrite JWord.W64.of_uintK.
                rewrite JWord.W64.of_uintK.
                rewrite JWord.W64.of_uintK.
                rewrite JWord.W64.of_uintK.
                simplify.

              rewrite /JWord.W64.(\umod).
              rewrite /JWord.W64.ulift2.
              rewrite JWord.W64.of_uintK.
              rewrite JWord.W64.of_uintK.
              simplify.
              rewrite JWord.W64.to_uint_shr.
            trivial.
              rewrite JWord.W64.to_uint_shl.
              smt().
              simplify.
              smt().

              rewrite /JWord.W64.SHIFT.SHL_64.
              simplify.
              rewrite /JWord.W64.shift_mask.
              rewrite /JWord.W4u8.truncateu8.
              simplify.

            have : (JWord.W32.to_uint
              (JWord.W32.WRingA.(-) (JWord.W32.of_int 15) z{hr}) %%
                256 %% 64 = 0) = false.
                rewrite /JWord.W32.(+).
                rewrite /JWord.W32.ulift2.
                rewrite /JWord.W32.([-]).
                rewrite /JWord.W32.ulift1.
                rewrite JWord.W32.of_uintK.
                rewrite JWord.W32.of_uintK.
                rewrite JWord.W32.of_uintK.
              smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
            move => temp.
              rewrite temp.
              simplify.

              rewrite /JWord.W64.SHIFT.rflags_OF.
              simplify.
              rewrite /JWord.W64.(\umod).
              rewrite /JWord.W64.ulift2.
              rewrite /JWord.W2u32.zeroextu64.
              rewrite /JWord.W64.(\ule).
              rewrite /JWord.W64.(`>>`).
              rewrite JWord.W64.of_uintK.
              rewrite JWord.W64.of_uintK.
              rewrite JWord.W64.to_uint_shr.
              smt().
              rewrite JWord.W64.to_uint_shl.
              smt().
              rewrite /JWord.W64.([-]).
              rewrite /JWord.W64.ulift1.
              simplify.
              rewrite /JWord.W64.(+).
              rewrite /JWord.W64.ulift2.
              rewrite JWord.W64.of_uintK.
              rewrite JWord.W64.of_uintK.
              rewrite JWord.W64.to_uint_shl.
              trivial.
              rewrite JWord.W64.to_uint_shl.
              smt().
              rewrite /JWord.W32.(+).
              rewrite /JWord.W32.ulift2.
              rewrite /JWord.W32.([-]).
              rewrite /JWord.W32.ulift1.
              rewrite JWord.W64.of_uintK.
              rewrite JWord.W32.of_uintK.
              rewrite JWord.W32.of_uintK.
              rewrite JWord.W32.of_uintK.
              simplify.

            have : (((15 + (- JWord.W32.to_uint z{hr}) %% 4294967296) %% 4294967296 %% 256 %%
                64)) = (((15 + (- JWord.W32.to_uint z{hr})))).
            clear H2 H6. (*Here we go again*)
              have m6x : JWord.W32.to_uint (JWord.W32.of_int 14) = 14 by rewrite JWord.W32.of_uintK.
have hz6 : JWord.W32.to_uint z{hr} <= 14 by smt(JWord.W32.uleE).
have hz0 := JWord.W32.to_uint_cmp z{hr}.
rewrite IntDiv.modzDmr (IntDiv.modz_small (15 - JWord.W32.to_uint z{hr})) 1:/# (IntDiv.modz_small (15 - JWord.W32.to_uint z{hr}) 256) 1:/# IntDiv.modz_small /#.
            move => temp2.
              rewrite temp2.
              have : ((15 - JWord.W32.to_uint z{hr})) <= 15.

              smt(JWord.W32.to_uint_cmp).
            move => bound1.
              have : 1 <= ((15 - JWord.W32.to_uint z{hr})).
              smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
            move => bound2.
              have := StdOrder.IntOrder.ler_weexpn2l 2 _ ((15 - JWord.W32.to_uint z{hr})) 15 _.
              trivial.
              smt().
            simplify.
            move => temp3.
            have : ((2 ^ (15 - JWord.W32.to_uint z{hr}) %% 18446744073709551616) = ((2 ^ (15 - JWord.W32.to_uint z{hr})))).
            

              smt(StdOrder.IntOrder.expr_gt0).
            move => temp4.
              rewrite temp4.
              have : (18446744073709551616) = 2 ^ 64.
              smt().
            move => mod64.

have : (JWord.W32.to_uint i{hr} %% 18446744073709551616 %%
  (2 ^ (15 - JWord.W32.to_uint z{hr}) %/ 2)) = (JWord.W32.to_uint i{hr} %%
  (2 ^ (15 - JWord.W32.to_uint z{hr}) %/ 2)).
  smt(JWord.W32.to_uint_cmp StdOrder.IntOrder.ler_weexpn2l).
move => temp5.
  rewrite temp5.

have : ((32768 +
 ((- 2 ^ (15 - JWord.W32.to_uint z{hr})) +
  JWord.W32.to_uint i{hr} %% (2 ^ (15 - JWord.W32.to_uint z{hr}) %/ 2)) %%
 18446744073709551616) %%
18446744073709551616) = ((32768 +
 ((- 2 ^ (15 - JWord.W32.to_uint z{hr})) +
  JWord.W32.to_uint i{hr} %% (2 ^ (15 - JWord.W32.to_uint z{hr}) %/ 2))) %%
   18446744073709551616).

   smt().
move => temp6.
   rewrite temp6.

   have : ((2 ^ (15 - JWord.W32.to_uint z{hr}) %/ 2)) <= 16384.
   smt().
move => bound3.
   have : (2 ^ 1) = 2.
   smt().
move => mod2.
   have : 2 <= (2 ^ (15 - JWord.W32.to_uint z{hr})).
   smt(StdOrder.IntOrder.ler_weexpn2l).
move => smash_bros.
have :0 < ((2 ^ (15 - JWord.W32.to_uint z{hr}) %/ 2)).
   smt().
move => bound4.

   have : (JWord.W32.to_uint i{hr} %% (2 ^ (15 - JWord.W32.to_uint z{hr}) %/ 2)) < 16384.
   smt().
move => random_bound.

have : ((32768 +
 ((- 2 ^ (15 - JWord.W32.to_uint z{hr})) +
  JWord.W32.to_uint i{hr} %% (2 ^ (15 - JWord.W32.to_uint z{hr}) %/ 2))) %%
18446744073709551616) = ((32768 +
 ((- 2 ^ (15 - JWord.W32.to_uint z{hr})) +
   JWord.W32.to_uint i{hr} %% (2 ^ (15 - JWord.W32.to_uint z{hr}) %/ 2)))).
   smt().
move => temp7.
   rewrite temp7.
   smt().

   rewrite /JWord.W64.SHIFT.SHL_64.
   simplify.
have : (JWord.W64.shift_mask
              (JWord.W4u8.truncateu8 (JWord.W32.of_int 15)) =
              0) = false.
                rewrite /JWord.W4u8.truncateu8.
                rewrite /JWord.W64.shift_mask.
                smt().
            move => cond_false.
                rewrite cond_false.
                simplify.

            have : (JWord.W64.shift_mask
              (JWord.W4u8.truncateu8
                 (JWord.W32.WRingA.(-) (JWord.W32.of_int 15) z{hr})) =
               0) = false.
                   rewrite /JWord.W4u8.truncateu8.
                   rewrite /JWord.W32.(+).
                   rewrite /JWord.W32.ulift2.
                   rewrite /JWord.W32.([-]).
                   rewrite /JWord.W32.ulift1.
                   rewrite /JWord.W64.shift_mask.
                   simplify.
                   rewrite JWord.W32.of_uintK.
                   rewrite JWord.W32.of_uintK.
                   smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).

             move => cond_false_2.
                   rewrite cond_false_2.
                   simplify.
                   rewrite /JWord.W64.SHIFT.rflags_OF.
                   simplify.
                   rewrite JWord.W64.shlMP.
                   smt().
                   rewrite JWord.W64.shlMP.
                   smt().
                   rewrite /JUtils.(`<<`).
                   simplify.
             have : (0 <=
                   JWord.W32.to_uint (JWord.W32.WRingA.(-) (JWord.W32.of_int 15) z{hr})) = true.
                   smt(JWord.W32.to_uint_cmp).
             move => cond_true.
                   rewrite cond_true.
                   simplify.
             have : (0 <=
            JWord.W32.to_uint
              (JWord.W32.WRingA.(-) (JWord.W32.of_int 14) z{hr})) = true.
                smt(JWord.W32.to_uint_cmp).
            move => cond_true_2.
                rewrite cond_true_2.
                simplify.
                rewrite /JWord.W64.(`>>`).
                rewrite JWord.W64.shrDP.
                smt().
                rewrite /JWord.W4u8.truncateu8.
                rewrite /JWord.W2u32.zeroextu64.
                rewrite /JWord.W2u32.truncateu32.
                rewrite /JWord.W64.shift_mask.
                simplify.
                rewrite /JWord.W32.(\umod).
                rewrite /JWord.W32.ulift2.
                rewrite /JWord.W64.(+).
                rewrite /JWord.W64.ulift2.
                simplify.
                rewrite /JWord.W32.(+).
                rewrite /JWord.W32.ulift2.
                rewrite /JWord.W32.([-]).
                rewrite /JWord.W32.ulift1.
                rewrite /JWord.W64.(\umod).
                rewrite /JWord.W64.ulift2.

                rewrite JWord.W32.of_uintK.
                rewrite JWord.W32.of_uintK.
                rewrite JWord.W32.of_uintK.
                rewrite JWord.W32.of_uintK.
                rewrite JWord.W32.of_uintK.
                rewrite JWord.W32.of_uintK.
                rewrite JWord.W64.of_uintK.
                rewrite JWord.W64.of_uintK.
                rewrite JWord.W64.of_uintK.
                rewrite JWord.W64.of_uintK.
                rewrite JWord.W64.of_uintK.
                simplify.
                have :((15 + (- JWord.W32.to_uint z{hr}) %% 4294967296) %% 4294967296) = ((15 + (- JWord.W32.to_uint z{hr})) %% 4294967296).
                smt().
            move => temp.
                rewrite temp.
                have : ((14 + (- JWord.W32.to_uint z{hr}) %% 4294967296) %% 4294967296) = ((14 + (- JWord.W32.to_uint z{hr})) %% 4294967296).
                smt().
            move => temp2.
            rewrite temp2.

                have := StdOrder.IntOrder.ler_weexpn2l 2 _ ((15 - JWord.W32.to_uint z{hr})) 15 _.
                trivial.
                smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
                simplify.
            move => aux.
             have := StdOrder.IntOrder.ler_weexpn2l 2 _ (14 - JWord.W32.to_uint z{hr}) 14 _.
                trivial.
                smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
            simplify.
            move => aux2.

have : (32768 - 2 ^ ((15 - JWord.W32.to_uint z{hr}) %% 4294967296 %% 256 %% 64)) %%
            18446744073709551616 = ((32768 - 2 ^ ((15 - JWord.W32.to_uint z{hr})))).
                smt(JWord.W32.of_uintK StdOrder.IntOrder.expr_gt0).
            move => temp3.
                rewrite temp3.
                move : H6.
                rewrite /JWord.W32.(\ult).
                rewrite /JUtils.(`<<`).
            have : (0 <=
                JWord.W32.to_uint (JWord.W32.WRingA.(-) (JWord.W32.of_int 14) z{hr})) = true.
                                                     smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg).
            move => cond_true3.
                rewrite cond_true3.
                simplify.
                rewrite /JWord.W32.(+).
                rewrite /JWord.W32.ulift2.
                rewrite /JWord.W32.([-]).
                rewrite /JWord.W32.ulift1.
                rewrite JWord.W32.of_uintK.
                rewrite JWord.W32.of_uintK.
                rewrite JWord.W32.of_uintK.
                rewrite JWord.W32.of_uintK.
            simplify.

            have : 17 * 2 ^ ((14 + (- JWord.W32.to_uint z{hr}) %% 4294967296) %% 4294967296) %%
              4294967296 = 17 * 2 ^ ((14 + (- JWord.W32.to_uint z{hr}))).
                smt(JWord.W32.of_uintK StdOrder.IntOrder.expr_gt0).
            move => temp4.
            rewrite temp4.
            move => bound_i.

                have : (JWord.W32.to_uint i{hr} %% 18446744073709551616) = (JWord.W32.to_uint i{hr}).
                smt(JWord.W32.to_uint_cmp).
            move => temp5.
                rewrite temp5.

            have : (2 ^ ((15 - JWord.W32.to_uint z{hr}) %% 4294967296 %% 256 %% 64) %%
              18446744073709551616) = (2 ^ ((15 - JWord.W32.to_uint z{hr}))).
                smt(JWord.W32.of_uintK StdOrder.IntOrder.expr_gt0).
            move => temp6.
                rewrite temp6.
                have : (2 ^ (15 - JWord.W32.to_uint z{hr}) %/ 2 %% 18446744073709551616) = (2 ^ (15 - JWord.W32.to_uint z{hr}) %/ 2).
                smt().
            move => temp7.
                rewrite temp7.

            have : (((32768 - 2 ^ (15 - JWord.W32.to_uint z{hr}) +
    JWord.W32.to_uint i{hr} %% (2 ^ (15 - JWord.W32.to_uint z{hr}) %/ 2) %%
    18446744073709551616) %%
   18446744073709551616)) = (((32768 - 2 ^ (15 - JWord.W32.to_uint z{hr}) +
                JWord.W32.to_uint i{hr} %% (2 ^ (15 - JWord.W32.to_uint z{hr}) %/ 2)))).

                have m6x : JWord.W32.to_uint (JWord.W32.of_int 14) = 14 by rewrite JWord.W32.of_uintK.
have hz6 : JWord.W32.to_uint z{hr} <= 14 by smt(JWord.W32.uleE).
have hz0 := JWord.W32.to_uint_cmp z{hr}.
have hq2 : 2 ^ (15 - JWord.W32.to_uint z{hr}) %/ 2 = 2 ^ (14 - JWord.W32.to_uint z{hr}).
  rewrite (_: 15 - JWord.W32.to_uint z{hr} = (14 - JWord.W32.to_uint z{hr}) + 1) 1:/# StdOrder.IntOrder.Domain.exprS 1:/#.
  by rewrite mulzC IntDiv.mulzK.
have hq0 : 0 < 2 ^ (14 - JWord.W32.to_uint z{hr}) by apply StdOrder.IntOrder.expr_gt0.
have hr : 0 <= JWord.W32.to_uint i{hr} %% 2 ^ (14 - JWord.W32.to_uint z{hr}) < 2 ^ (14 - JWord.W32.to_uint z{hr}) by smt(IntDiv.modz_ge0 IntDiv.ltz_pmod).
rewrite hq2 !(IntDiv.modz_small (JWord.W32.to_uint i{hr} %% _)) 1:/#; smt(IntDiv.modz_small).
            move => temp8.
            rewrite temp8.

                have m6x : JWord.W32.to_uint (JWord.W32.of_int 14) = 14 by rewrite JWord.W32.of_uintK.
have hz6 : JWord.W32.to_uint z{hr} <= 14 by smt(JWord.W32.uleE).
have hz0 := JWord.W32.to_uint_cmp z{hr}.
have hq2 : 2 ^ (15 - JWord.W32.to_uint z{hr}) %/ 2 = 2 ^ (14 - JWord.W32.to_uint z{hr}).
  rewrite (_: 15 - JWord.W32.to_uint z{hr} = (14 - JWord.W32.to_uint z{hr}) + 1) 1:/# StdOrder.IntOrder.Domain.exprS 1:/#.
  by rewrite mulzC IntDiv.mulzK.
have e7 : (15 - JWord.W32.to_uint z{hr}) %% 4294967296 = 15 - JWord.W32.to_uint z{hr} by rewrite IntDiv.modz_small /#.
have e6 : (14 - JWord.W32.to_uint z{hr}) %% 4294967296 = 14 - JWord.W32.to_uint z{hr} by rewrite IntDiv.modz_small /#.
have p6 : 2 ^ (14 - JWord.W32.to_uint z{hr}) <= 16384 by apply (StdOrder.IntOrder.ler_weexpn2l 2 _ (14 - JWord.W32.to_uint z{hr}) 14) => /#.
have e6b : 2 ^ (14 - JWord.W32.to_uint z{hr}) %% 4294967296 = 2 ^ (14 - JWord.W32.to_uint z{hr}) by rewrite IntDiv.modz_small; smt(StdOrder.IntOrder.expr_gt0).
by rewrite e7 e6 e6b hq2.
qed .

lemma fors_skgen_proof _sk _b_sk _skseed _b_skseed _pkseed _b_pkseed _adrs _b_adrs _idx :
      (fors_skgen_spec _sk _b_sk _skseed _b_skseed _pkseed _b_pkseed 
      _adrs _b_adrs _idx).
proof.
    
rewrite /fors_skgen_spec .
proc; auto .
ecall (__PRF_proof param_11 b_param param_10 (BArray24.init_arr
                                             (JWord.W8.of_int 255)) param_9 
       (BArray24.init_arr (JWord.W8.of_int 255)) param_8 (BArray32.init_arr
                                                   (JWord.W8.of_int 255))).
auto .
ecall (__adrs_set_tree_index_proof param_7 (BArray32.init_arr (JWord.W8.of_int 255)
                                           ) param_6).
auto .
ecall (__adrs_set_key_pair_addr_proof param_5 (BArray32.init_arr
                                              (JWord.W8.of_int 255)) param_4).
auto .
ecall (__adrs_get_key_pair_addr_proof param_3 (BArray32.init_arr
                                              (JWord.W8.of_int 255))).
auto .
ecall (__adrs_set_type_and_clear_proof param_2 (BArray32.init_arr
                                               (JWord.W8.of_int 255)) param_1).
auto .
ecall (__adrs_clone_proof param_0 b_param_0 param (BArray32.init_arr
                                                  (JWord.W8.of_int 255))).
auto .
smt(BArray32.init_arrP BArray24.init_arrP).
qed .

lemma __fors_skgen_proof _sk _b_sk _skseed _b_skseed _pkseed _b_pkseed _adrs _b_adrs _idx :
      (__fors_skgen_spec _sk _b_sk _skseed _b_skseed _pkseed _b_pkseed 
      _adrs _b_adrs _idx).
      proof.
rewrite /__fors_skgen_spec .
proc; auto .
ecall (fors_skgen_proof param_3 b_param param_2 (BArray24.init_arr
                                                (JWord.W8.of_int 255)) param_1 
       (BArray24.init_arr (JWord.W8.of_int 255)) param_0 (BArray32.init_arr
                                                   (JWord.W8.of_int 255)) param).
auto .
smt(BArray32.init_arrP BArray24.init_arrP).
qed .

(* ---- arithmetic helpers for fors_node ---- *)
lemma pow2_split (a b : int) : 0 <= a => 0 <= b => 2 ^ (a + b) = 2 ^ a * 2 ^ b.
proof. move => ha hb. by rewrite StdOrder.IntOrder.Domain.exprD_nneg. qed.

lemma pow2_A : 2 ^ 14 = 16384.
proof. smt(StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.Domain.expr0). qed.

lemma pow2_leA (k : int) : 0 <= k <= 14 => 2 ^ k <= 16384.
proof.
move => hk. have h : 2 ^ k <= 2 ^ 14 by apply StdOrder.IntOrder.ler_weexpn2l.
by rewrite -pow2_A.
qed.

lemma shl1 (k : int) : 0 <= k => JUtils.(`<<`) 1 k = 2 ^ k.
proof. move => hk. by rewrite /JUtils.(`<<`) hk /=. qed.

lemma fors_node_bound (n ii zz ll : int) :
  0 <= zz <= 14 => 1 <= ll <= zz =>
  ii < 17 * 2 ^ (14 - zz) =>
  n < (ii + 1) * 2 ^ (zz - ll) =>
  n * 2 < 17 * 2 ^ (15 - ll) /\ 17 * 2 ^ (15 - ll) <= 17 * 16384.
proof.
move => hz hl hi hn.
have hE : 2 ^ (14 - zz) * 2 ^ (zz - ll + 1) = 2 ^ (15 - ll).
+ rewrite -pow2_split 1,2:/#. congr; ring.
have hd : 2 ^ (zz - ll + 1) = 2 ^ (zz - ll) * 2.
+ rewrite (pow2_split (zz - ll) 1) 1,2:/#. by rewrite expr1.
split; last by smt(pow2_leA).
have h1 : n * 2 < (ii + 1) * 2 ^ (zz - ll + 1) by rewrite hd; smt().
have h2 : (ii + 1) * 2 ^ (zz - ll + 1) <= (17 * 2 ^ (14 - zz)) * 2 ^ (zz - ll + 1).
+ apply StdOrder.IntOrder.ler_wpmul2r; smt(StdOrder.IntOrder.expr_ge0).
smt().
qed.

lemma pow2_A1 : 2 ^ 15 = 32768.
proof. smt(StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.Domain.expr0). qed.

lemma pow2_leA1 (k : int) : 0 <= k <= 15 => 2 ^ k <= 32768.
proof.
move => hk. have h : 2 ^ k <= 2 ^ 15 by apply StdOrder.IntOrder.ler_weexpn2l.
by rewrite -pow2_A1.
qed.

lemma fors_child_addr (n ii zz ll : int) :
  0 <= zz <= 14 => 1 <= ll <= zz => 0 <= ii =>
  ii * 2 ^ (zz - ll) <= n => n < (ii + 1) * 2 ^ (zz - ll) =>
  (n * 2) %% 2 ^ (15 - ll)
    = (ii %% 2 ^ (14 - zz)) * 2 ^ (zz - ll + 1) + 2 * (n - ii * 2 ^ (zz - ll)).
proof.
move => hz hl hi0 hn1 hn2.
pose q := 2 ^ (zz - ll + 1).
pose k := 2 ^ (14 - zz).
have hq : 0 < q by rewrite /q; smt(StdOrder.IntOrder.expr_gt0).
have hk : 0 < k by rewrite /k; smt(StdOrder.IntOrder.expr_gt0).
have hqe : q = 2 ^ (zz - ll) * 2.
+ rewrite /q (pow2_split (zz - ll) 1) 1,2:/#. by rewrite expr1.
have hM : 2 ^ (15 - ll) = q * k.
+ rewrite /q /k -pow2_split 1,2:/#.
  by have -> : zz - ll + 1 + (14 - zz) = 15 - ll by ring.
pose d := 2 * (n - ii * 2 ^ (zz - ll)).
have hdb : 0 <= d < q by rewrite /d hqe; smt().
have hne : n * 2 = ii * q + d by rewrite /d hqe; ring.
have hmk : 0 <= ii %% k < k by smt(modz_ge0 ltz_pmod).
have hb : (ii %% k) * q + d < q * k.
+ have : (ii %% k) * q <= (k - 1) * q by apply StdOrder.IntOrder.ler_wpmul2r; smt().
  smt().
have hsplit : ii * q + d = (ii %/ k) * (q * k) + ((ii %% k) * q + d).
+ have hde := divz_eq ii k.
  have -> : ii * q = ((ii %/ k) * k + ii %% k) * q by rewrite -hde.
  ring.
rewrite hM hne hsplit modzMDl modz_small 2://.
smt().
qed.

lemma shl64_val (w : W32.t) (k : int) :
  0 <= k <= 14 => W32.to_uint w = k =>
  (SHL_64 W64.one (truncateu8 w)).`6 = W64.of_int (2 ^ k).
proof.
move => hk hw.
rewrite /SHL_64 /shift_mask /truncateu8 /= hw.
have hm : k %% 256 %% 64 = k by smt().
rewrite hm.
case (k = 0) => hc.
+ rewrite hc /=. done.
rewrite /rflags_OF /=.
by rewrite W64.shlMP 1:/# /=.
qed.

lemma fors_node_mod (n ii zz ll : int) :
  0 <= zz <= 14 => 0 <= ll <= zz => 0 <= ii =>
  ii * 2 ^ (zz - ll) <= n => n < (ii + 1) * 2 ^ (zz - ll) =>
  n %% 2 ^ (14 - ll)
    = (ii %% 2 ^ (14 - zz)) * 2 ^ (zz - ll) + (n - ii * 2 ^ (zz - ll)).
proof.
move => hz hl hi0 hn1 hn2.
pose q := 2 ^ (zz - ll).
pose k := 2 ^ (14 - zz).
have hq : 0 < q by rewrite /q; smt(StdOrder.IntOrder.expr_gt0).
have hk : 0 < k by rewrite /k; smt(StdOrder.IntOrder.expr_gt0).
have hM : 2 ^ (14 - ll) = q * k.
+ rewrite /q /k -pow2_split 1,2:/#.
  by have -> : zz - ll + (14 - zz) = 14 - ll by ring.
pose d := n - ii * 2 ^ (zz - ll).
have hdb : 0 <= d < q by rewrite /d /q; smt().
have hne : n = ii * q + d by rewrite /d /q; ring.
have hmk : 0 <= ii %% k < k by smt(modz_ge0 ltz_pmod).
have hb : (ii %% k) * q + d < q * k.
+ have : (ii %% k) * q <= (k - 1) * q by apply StdOrder.IntOrder.ler_wpmul2r; smt().
  smt().
have hsplit : ii * q + d = (ii %/ k) * (q * k) + ((ii %% k) * q + d).
+ have hde := divz_eq ii k.
  have -> : ii * q = ((ii %/ k) * k + ii %% k) * q by rewrite -hde.
  ring.
rewrite hM {1}hne hsplit modzMDl modz_small 2://.
smt().
qed.

lemma fors_children_in_block (lab n ii zz ll : int) :
  0 <= zz <= 14 => 1 <= ll <= zz => 0 <= ii =>
  ii * 2 ^ (zz - ll) <= n => n < (ii + 1) * 2 ^ (zz - ll) =>
  lab = 32768 - 2 ^ (16 - ll) + (n * 2) %% 2 ^ (15 - ll) =>
     24 * (32768 - 2 ^ (16 - ll))
   + 24 * (ii %% 2 ^ (14 - zz)) * 2 ^ (zz - ll + 1) <= 24 * lab
  /\ 24 * lab + 48
     <= 24 * (32768 - 2 ^ (16 - ll))
      + 24 * (ii %% 2 ^ (14 - zz)) * 2 ^ (zz - ll + 1)
      + 24 * 2 ^ (zz - ll + 1)
  /\ 0 <= lab <= 32764.
proof.
move => hz hl hi0 hn1 hn2 hlab.
have hdec : (n * 2) %% 2 ^ (15 - ll)
          = (ii %% 2 ^ (14 - zz)) * 2 ^ (zz - ll + 1) + 2 * (n - ii * 2 ^ (zz - ll)).
+ apply fors_child_addr; smt().
pose r := ii %% 2 ^ (14 - zz).
pose q := 2 ^ (zz - ll + 1).
pose e := n - ii * 2 ^ (zz - ll).
have hq : q = 2 ^ (zz - ll) * 2.
+ rewrite /q (pow2_split (zz - ll) 1) 1,2:/#. by rewrite expr1.
have heb : 0 <= e < 2 ^ (zz - ll) by smt().
have hlab2 : lab = 32768 - 2 ^ (16 - ll) + (r * q + 2 * e) by rewrite hlab hdec.
have hqp : 2 ^ (15 - ll) = q * 2 ^ (14 - zz).
+ rewrite /q -pow2_split 1,2:/#.
  by have -> : zz - ll + 1 + (14 - zz) = 15 - ll by ring.
have hrb : 0 <= r < 2 ^ (14 - zz) by smt(modz_ge0 ltz_pmod StdOrder.IntOrder.expr_gt0).
have h1 : r * q <= (2 ^ (14 - zz) - 1) * q.
+ apply StdOrder.IntOrder.ler_wpmul2r; smt(StdOrder.IntOrder.expr_ge0).
have h2 : (2 ^ (14 - zz) - 1) * q + q = 2 ^ (15 - ll) by rewrite hqp; ring.
have hub : r * q + 2 * e <= 2 ^ (15 - ll) - 2 by smt().
have hp11 : 2 ^ (16 - ll) = 2 * 2 ^ (15 - ll).
+ have -> : 16 - ll = (15 - ll) + 1 by ring.
  rewrite (pow2_split (15 - ll) 1) 1,2:/#. by rewrite expr1; ring.
have hp10 : 2 <= 2 ^ (15 - ll) <= 16384 by smt(pow2_leA StdOrder.IntOrder.ler_weexpn2l).
smt().
qed.

lemma forest_label_val_int (rr : W64.t) (nn : W32.t) (e : int) :
  0 <= e <= 14 =>
  0 <= W64.to_uint rr <= 32766 =>
  truncateu32 rr = W32.of_int (32768 - 2 ^ (e + 1)) + (nn \umod W32.of_int (2 ^ e)) =>
  W64.to_uint rr = 32768 - 2 ^ (e + 1) + (W32.to_uint nn %% 2 ^ e).
proof.
move => he hr hv.
have hpe : 1 <= 2 ^ e <= 16384 by smt(pow2_leA StdOrder.IntOrder.exprn_ege1).
have hpe1 : 2 ^ (e + 1) = 2 ^ e * 2.
+ rewrite (pow2_split e 1) 1,2:/#. by rewrite expr1.
move: hv hpe hpe1. pose P := 2 ^ e. pose Q := 2 ^ (e + 1). move => hv hpe hpe1.
have hnn : 0 <= W32.to_uint nn %% P < P by smt(modz_ge0 ltz_pmod).
have hmod : W32.to_uint (nn \umod W32.of_int P) = W32.to_uint nn %% P.
+ rewrite W32.umodE /ulift2 !W32.of_uintK; smt().
have hL : W32.to_uint (truncateu32 rr) = W64.to_uint rr.
+ rewrite to_uint_truncateu32; smt().
have hR : W32.to_uint (W32.of_int (32768 - Q) + (nn \umod W32.of_int P))
        = 32768 - Q + (W32.to_uint nn %% P).
+ rewrite W32.to_uintD_small hmod W32.of_uintK; smt().
by rewrite -hL hv hR.
qed.

lemma forest_label_val0 (rr : W64.t) (nn : W32.t) :
  0 <= W64.to_uint rr <= 32766 =>
  truncateu32 rr = (nn \umod W32.of_int 16384) =>
  W64.to_uint rr = W32.to_uint nn %% 16384.
proof.
move => hr hv.
have hnn : 0 <= W32.to_uint nn %% 16384 < 16384 by smt(modz_ge0 ltz_pmod).
have hmod : W32.to_uint (nn \umod W32.of_int 16384) = W32.to_uint nn %% 16384.
+ rewrite W32.umodE /ulift2 !W32.of_uintK; smt().
have hL : W32.to_uint (truncateu32 rr) = W64.to_uint rr.
+ rewrite to_uint_truncateu32; smt().
by rewrite -hL hv hmod.
qed.

lemma forest_label_val_shl (rr : W64.t) (nn : W32.t) (e : int) :
  0 <= e <= 14 =>
  0 <= W64.to_uint rr <= 32766 =>
  truncateu32 rr = W32.of_int (JUtils.(`<<`) 1 15 - JUtils.(`<<`) 1 (e + 1))
                 + (nn \umod W32.of_int (JUtils.(`<<`) 1 e)) =>
  W64.to_uint rr = 32768 - 2 ^ (e + 1) + (W32.to_uint nn %% 2 ^ e).
proof.
move => he hr hv.
apply (forest_label_val_int rr nn e) => //.
move: hv. by rewrite (shl1 15) 1:// (shl1 (e + 1)) 1:/# (shl1 e) 1:/# pow2_A1.
qed.

lemma fors_node_proof _root _b_root _skseed _b_skseed _i _z _pkseed _b_pkseed _adrs _b_adrs :
      (fors_node_spec _root _b_root _skseed _b_skseed _i _z _pkseed _b_pkseed
      _adrs _b_adrs).
proof.
  rewrite /fors_node_spec .
  proc; auto .
  ecall (__copy_nbytes_proof param_31 b_param_0 param_30 b_param).
  auto . 
  unroll 64.
  seq 58: #pre. by auto.
  sp.
  if.
  + while (0 < to_uint layer<= to_uint z + 1 /\
           0<= to_uint i < 17 * (JUtils.(`<<`) 1 (14- to_uint z)) /\ 
           to_uint z <= 14 /\ b_node_addr /\ 0 <= to_uint node_addr <= 786408 - 24 /\ 
           BArray786408.is_init b_flat_tree (to_uint node_addr) 24 /\
           BArray24.is_init _b_pkseed 0 24 /\ BArray24.is_init _b_skseed 0 24 /\
           to_uint node_addr = 24 * (32768 - 2 ^ (16 - to_uint layer))
           + 24 * ((to_uint i %% 2 ^ (14 - to_uint z)) + 1)
           * 2 ^ (to_uint z - to_uint layer + 1) - 24 /\
           (forall (x : int), 0 <= x < to_uint layer =>
           BArray786408.is_init b_flat_tree (  24 * (32768 - 2 ^ (15 - x)) + 24 * 
           (to_uint i %% 2 ^ (14 - to_uint z)) * 2 ^ (to_uint z - x))(24 * 2 ^ (to_uint z - x)))).   
    + auto. 
      while (0 < to_uint layer <= to_uint z /\
             0<= to_uint i < 17 * (JUtils.(`<<`) 1 (14- to_uint z)) /\ to_uint z <= 14 /\ 
             0<= to_uint node /\ b_node_addr /\ 0 <= to_uint node_addr <= 786408 - 24 /\
             BArray786408.is_init b_flat_tree (to_uint node_addr) 24 /\ 
             BArray24.is_init _b_pkseed 0 24 /\ BArray24.is_init _b_skseed 0 24 /\
to_uint i * 2 ^ (to_uint z - to_uint layer) <= to_uint node
               <= (to_uint i + 1) * 2 ^ (to_uint z - to_uint layer) /\
             to_uint rightmost = (to_uint i + 1) * 2 ^ (to_uint z - to_uint layer) /\
             (to_uint i * 2 ^ (to_uint z - to_uint layer) < to_uint node =>
                to_uint node_addr =
                  24 * (32768 - 2 ^ (15 - to_uint layer))
                + 24 * (to_uint i %% 2 ^ (14 - to_uint z)) * 2 ^ (to_uint z - to_uint layer)
                + 24 * (to_uint node - to_uint i * 2 ^ (to_uint z - to_uint layer))
                - 24) /\
BArray786408.is_init b_flat_tree
               (  24 * (32768 - 2 ^ (15 - to_uint layer))
                + 24 * (to_uint i %% 2 ^ (14 - to_uint z)) * 2 ^ (to_uint z - to_uint layer))
               (24 * (to_uint node - to_uint i * 2 ^ (to_uint z - to_uint layer))) /\
 (forall (x : int), 0 <= x < to_uint layer =>
                BArray786408.is_init b_flat_tree
                  (  24 * (32768 - 2 ^ (15 - x))
                   + 24 * (to_uint i %% 2 ^ (14 - to_uint z)) * 2 ^ (to_uint z - x))
                  (24 * 2 ^ (to_uint z - x)))

     ).
      + auto. if. exfalso. move => &m />.  by rewrite W32.to_uint_eq /= /#.
        auto. 
        ecall (__H_proof param_29 b_param_3 param_28 (BArray24.init_arr
               (W8.of_int 255)) param_27 (BArray32.init_arr (W8.of_int 255)) param_26
               (BArray24.init_arr (W8.of_int 255)) param_25 (BArray24.init_arr (W8.of_int 255))).
        auto .
        ecall (__forest_label_proof param_24 param_23).
        auto .
        ecall (__adrs_set_tree_index_proof param_22 (BArray32.init_arr
                                            (W8.of_int 255)) param_21).
        auto .
        ecall (__adrs_set_tree_height_proof param_20 (BArray32.init_arr
                                             (W8.of_int 255)) param_19).
        auto .
        ecall (__copy_nbytes_proof param_18 b_param_5 param_17 b_param_4).
        auto .
        ecall (__copy_nbytes_proof param_16 b_param_7 param_15 b_param_6).
        auto .
        ecall (__forest_label_proof param_14 param_13).
        auto . rewrite /is_init /= => /> &m 16?. rewrite !ultE !uleE /= => *.
        have hNB := fors_node_bound (to_uint node{m}) (to_uint i{m}) (to_uint z{m})
                                    (to_uint layer{m}) _ _ _ _.
        + smt(W32.to_uint_cmp).
        + smt().
        + rewrite -shl1 1:/#; smt().
        + smt().
        split. rewrite !to_uintB /=. rewrite uleE /=. smt(). rewrite uleE /=. rewrite !to_uintB /=. rewrite uleE /=. smt(). smt(). rewrite uleE /=. smt().
        + rewrite !to_uintM_small /=. smt(). split. smt(W32.to_uint_cmp).
          rewrite W32.of_uintK shl1 1:/# /=. smt().
        move => 4?.
        move => result0 hpnz0 hlo0 hhi0 hv0 hv0'.
        have hR0 : 0 <= to_uint result0 <= 32766.
        + move: hlo0 hhi0. rewrite !uleE /=. smt(W64.to_uint_cmp).
        have hM0 : to_uint (result0 * (W64.of_int 24)) = to_uint result0 * 24.
        + rewrite to_uintM_small /=; smt().
        have hl1 : to_uint (layer{m} - W32.one) = to_uint layer{m} - 1.
        + rewrite W32.to_uintB /=. rewrite uleE /=; smt(). done.
        have he1 : to_uint (W32.of_int 15 - (layer{m} - W32.one)) = 16 - to_uint layer{m}.
        + rewrite W32.to_uintB /=. rewrite uleE hl1 /=; smt(). rewrite hl1; smt().
        have he2 : to_uint (W32.of_int 14 - (layer{m} - W32.one)) = 15 - to_uint layer{m}.
        + rewrite W32.to_uintB /=. rewrite uleE hl1 /=; smt(). rewrite hl1; smt().
        have hnn2 : to_uint (node{m} * W32.of_int 2) = to_uint node{m} * 2.
        + rewrite to_uintM_small /=; smt().
        have hE : 16 - to_uint layer{m} = 15 - to_uint layer{m} + 1 by ring.
        have hA := forest_label_val_shl result0 (node{m} * W32.of_int 2)
                                        (15 - to_uint layer{m}) _ _ _.
        + smt().
        + smt().
        + move: hv0. by rewrite he1 he2 hE.
        have hval0 : to_uint result0
                   = 32768 - 2 ^ (16 - to_uint layer{m})
                   + (to_uint node{m} * 2) %% 2 ^ (15 - to_uint layer{m}).
        + move: hA. by rewrite hnn2 hE.
        have hFA : forall (x : int), 0 <= x < to_uint layer{m} =>
                     forall (i0 : int),
                       24 * (32768 - 2 ^ (15 - x))
                     + 24 * (to_uint i{m} %% 2 ^ (14 - to_uint z{m}))
                         * 2 ^ (to_uint z{m} - x) <= i0 =>
                       i0 < 24 * (32768 - 2 ^ (15 - x))
                          + 24 * (to_uint i{m} %% 2 ^ (14 - to_uint z{m}))
                              * 2 ^ (to_uint z{m} - x)
                          + 24 * 2 ^ (to_uint z{m} - x) =>
                       BArray786408.is_init_cell b_flat_tree{m} i0 by assumption.
        have hPart : forall (i0 : int),
                       24 * (32768 - 2 ^ (15 - to_uint layer{m}))
                     + 24 * (to_uint i{m} %% 2 ^ (14 - to_uint z{m}))
                         * 2 ^ (to_uint z{m} - to_uint layer{m}) <= i0 =>
                       i0 < 24 * (32768 - 2 ^ (15 - to_uint layer{m}))
                          + 24 * (to_uint i{m} %% 2 ^ (14 - to_uint z{m}))
                              * 2 ^ (to_uint z{m} - to_uint layer{m})
                          + 24 * (to_uint node{m}
                                  - to_uint i{m}
                                    * 2 ^ (to_uint z{m} - to_uint layer{m})) =>
                       BArray786408.is_init_cell b_flat_tree{m} i0 by assumption.
        have hFAL : forall (i0 : int),
                       24 * (32768 - 2 ^ (16 - to_uint layer{m}))
                     + 24 * (to_uint i{m} %% 2 ^ (14 - to_uint z{m}))
                         * 2 ^ (to_uint z{m} - to_uint layer{m} + 1) <= i0 =>
                       i0 < 24 * (32768 - 2 ^ (16 - to_uint layer{m}))
                          + 24 * (to_uint i{m} %% 2 ^ (14 - to_uint z{m}))
                              * 2 ^ (to_uint z{m} - to_uint layer{m} + 1)
                          + 24 * 2 ^ (to_uint z{m} - to_uint layer{m} + 1) =>
                       BArray786408.is_init_cell b_flat_tree{m} i0.
        + have h := hFA (to_uint layer{m} - 1) _; first smt().
          have -> : 16 - to_uint layer{m} = 15 - (to_uint layer{m} - 1) by ring.
          have -> : to_uint z{m} - to_uint layer{m} + 1
                  = to_uint z{m} - (to_uint layer{m} - 1) by ring.
          exact h.
        have hIB := fors_children_in_block (to_uint result0) (to_uint node{m})
                      (to_uint i{m}) (to_uint z{m}) (to_uint layer{m}) _ _ _ _ _ _.
        + smt().
        + smt().
        + smt().
        + smt().
        + smt().
        + exact hval0.
        have hM0' : to_uint (result0 * (W64.of_int 24) + W64.of_int 24)
                  = to_uint result0 * 24 + 24.
        + rewrite to_uintD_small hM0 /=; smt().
        have hP9 : 2 ^ (15 - to_uint layer{m}) = 2 * 2 ^ (14 - to_uint layer{m}).
        + have -> : 15 - to_uint layer{m} = 14 - to_uint layer{m} + 1 by ring.
          rewrite (pow2_split (14 - to_uint layer{m}) 1) 1,2:/#. by rewrite expr1; ring.
        have hNn : to_uint node{m} < 17 * 2 ^ (14 - to_uint layer{m}) by smt().
        have hUB : 17 * 2 ^ (14 - to_uint layer{m}) <= 278528 by smt().
        have he3 : to_uint (W32.of_int 14 - layer{m}) = 14 - to_uint layer{m}.
        + rewrite W32.to_uintB /=. rewrite uleE /=; smt(). done.
        have he4 : to_uint (W32.of_int 15 - layer{m}) = 15 - to_uint layer{m}.
        + rewrite W32.to_uintB /=. rewrite uleE /=; smt(). done.
        split. smt().
        move => *. split.
        + move => i0 ha hb.
          rewrite SBArray786408_24.SBArray786408_24.is_init_cell_get 1,2:/#.
          apply hFAL; smt().
        move => *. split. split. smt(W64.to_uint_cmp).
        + rewrite to_uintD_small to_uintM_small /=. smt(). smt(). smt(). smt().
        move => *. split.
        + move => i0 ha hb.
          rewrite SBArray786408_24.SBArray786408_24.is_init_cell_get 1,2:/#.
          apply hFAL; smt().
        move => *. split.  smt(BArray32.init_arrP BArray24.init_arrP).
        move => *. split.
        + rewrite he3 shl1 1:/# W32.of_uintK /=; smt(W32.to_uint_cmp).
        move => 4?.
        move => result5 hpnz5 hlo5 hhi5 hv5 hv5'.
        have hR5 : 0 <= to_uint result5 <= 32766.
        + move: hlo5 hhi5. rewrite !uleE /=. smt(W64.to_uint_cmp).
        have hM5 : to_uint (result5 * (W64.of_int 24)) = to_uint result5 * 24.
        + rewrite to_uintM_small /=; smt().
        have hE9 : 15 - to_uint layer{m} = 14 - to_uint layer{m} + 1 by ring.
        have hA5 := forest_label_val_shl result5 node{m} (14 - to_uint layer{m}) _ _ _.
        + smt().
        + smt().
        + move: hv5. by rewrite he3 he4 hE9.
        have hval5 : to_uint result5
                   = 32768 - 2 ^ (15 - to_uint layer{m})
                   + to_uint node{m} %% 2 ^ (14 - to_uint layer{m}).
        + move: hA5. by rewrite hE9.
        split. smt().
        move => 2?.
        split; 1: smt(BArray24.init_arrP).
        move => _ result6 ?.
        have hnode1 : to_uint (node{m} + W32.one) = to_uint node{m} + 1.
        + rewrite to_uintD_small /=; smt().
        have hmodn : to_uint node{m} %% 2 ^ (14 - to_uint layer{m})
                   = (to_uint i{m} %% 2 ^ (14 - to_uint z{m}))
                       * 2 ^ (to_uint z{m} - to_uint layer{m})
                   + (to_uint node{m}
                      - to_uint i{m} * 2 ^ (to_uint z{m} - to_uint layer{m})).
        + apply fors_node_mod; smt().
        have hAddr : to_uint (result5 * (W64.of_int 24))
                   = 24 * (32768 - 2 ^ (15 - to_uint layer{m}))
                   + 24 * (to_uint i{m} %% 2 ^ (14 - to_uint z{m}))
                       * 2 ^ (to_uint z{m} - to_uint layer{m})
                   + 24 * (to_uint node{m}
                           - to_uint i{m} * 2 ^ (to_uint z{m} - to_uint layer{m})).
        + rewrite hM5 hval5 hmodn; ring.
        split. smt().
        split. smt().
        split.
        + move => i0 ha hb.
          rewrite SBArray786408_24.SBArray786408_24.is_init_cell_set.
          smt(BArray32.init_arrP BArray24.init_arrP).
        split. smt().
        split. smt().
        split.
        + move => i0 ha hb.
          rewrite SBArray786408_24.SBArray786408_24.is_init_cell_set.
          case (to_uint (result5 * (W64.of_int 24)) <= i0 <
                24 + to_uint (result5 * (W64.of_int 24)) /\ 0 <= i0 < 786408) => hc /=.
          + smt(BArray32.init_arrP BArray24.init_arrP).
          apply hPart; smt().
        move => x hx1 hx2 i0 ha hb.
        rewrite SBArray786408_24.SBArray786408_24.is_init_cell_set.
        case (to_uint (result5 * (W64.of_int 24)) <= i0 <
              24 + to_uint (result5 * (W64.of_int 24)) /\ 0 <= i0 < 786408) => hc /=.
        + smt(BArray32.init_arrP BArray24.init_arrP).
        apply (hFA x); smt().
      auto.
      rewrite /is_init /= => /> &m 6?. rewrite !uleE /= => *.
      have hzl : to_uint (z{m} - layer{m}) = to_uint z{m} - to_uint layer{m}.
      + rewrite W32.to_uintB /=. rewrite uleE /=; smt(). done.
      have hSH : (SHL_64 W64.one (truncateu8 (z{m} - layer{m}))).`6
               = W64.of_int (2 ^ (to_uint z{m} - to_uint layer{m})).
      + apply (shl64_val (z{m} - layer{m})); smt().
      have hpzl : 1 <= 2 ^ (to_uint z{m} - to_uint layer{m}) <= 16384
        by smt(pow2_leA StdOrder.IntOrder.exprn_ege1).
      have hT : truncateu32 (SHL_64 W64.one (truncateu8 (z{m} - layer{m}))).`6
              = W32.of_int (2 ^ (to_uint z{m} - to_uint layer{m})).
      + rewrite hSH. apply W32.to_uint_eq.
        rewrite to_uint_truncateu32 W32.of_uintK W64.of_uintK; smt().
      have hsplitp : 2 ^ (14 - to_uint z{m}) * 2 ^ (to_uint z{m} - to_uint layer{m})
                   = 2 ^ (14 - to_uint layer{m}).
      + rewrite -pow2_split 1,2:/#.
        by have -> : 14 - to_uint z{m} + (to_uint z{m} - to_uint layer{m})
                   = 14 - to_uint layer{m} by ring.
      have hp9l : 2 ^ (14 - to_uint layer{m}) <= 16384 by smt(pow2_leA).
      have hI35 : to_uint i{m} < 17 * 2 ^ (14 - to_uint z{m}).
      + rewrite -shl1 1:/#; smt().
      have hbnd : to_uint i{m} * 2 ^ (to_uint z{m} - to_uint layer{m}) <= 278528.
      + have h1 : to_uint i{m} * 2 ^ (to_uint z{m} - to_uint layer{m})
                <= (17 * 2 ^ (14 - to_uint z{m})) * 2 ^ (to_uint z{m} - to_uint layer{m}).
        + apply StdOrder.IntOrder.ler_wpmul2r; smt(StdOrder.IntOrder.expr_ge0).
        smt().
      have hTi : to_uint (W32.of_int (2 ^ (to_uint z{m} - to_uint layer{m})) * i{m})
               = to_uint i{m} * 2 ^ (to_uint z{m} - to_uint layer{m}).
      + rewrite to_uintM_small W32.of_uintK; smt().
      have hTr : to_uint (W32.of_int (2 ^ (to_uint z{m} - to_uint layer{m}))
                          + W32.of_int (2 ^ (to_uint z{m} - to_uint layer{m})) * i{m})
               = (to_uint i{m} + 1) * 2 ^ (to_uint z{m} - to_uint layer{m}).
      + rewrite to_uintD_small hTi W32.of_uintK; smt().
      split.
      + rewrite !hT hTi hTr; smt().
      move => /> b_flat_tree0 b_node_addr0 node0 node_addr0 *.
      have hl1 : to_uint (layer{m} + W32.one) = to_uint layer{m} + 1.
      + rewrite to_uintD_small /=; smt(W32.to_uint_cmp).
      have hnode0 : to_uint node0
                  = (to_uint i{m} + 1) * 2 ^ (to_uint z{m} - to_uint layer{m}).
      + smt(W32.ultE).
      have hnaeq : to_uint node_addr0
                 = 24 * (32768 - 2 ^ (15 - to_uint layer{m}))
                 + 24 * (to_uint i{m} %% 2 ^ (14 - to_uint z{m}))
                     * 2 ^ (to_uint z{m} - to_uint layer{m})
                 + 24 * (to_uint node0
                         - to_uint i{m} * 2 ^ (to_uint z{m} - to_uint layer{m})) - 24.
      + smt().
      have hpart0 : forall (i0 : int),
             24 * (32768 - 2 ^ (15 - to_uint layer{m}))
           + 24 * (to_uint i{m} %% 2 ^ (14 - to_uint z{m}))
               * 2 ^ (to_uint z{m} - to_uint layer{m}) <= i0 =>
             i0 < 24 * (32768 - 2 ^ (15 - to_uint layer{m}))
                + 24 * (to_uint i{m} %% 2 ^ (14 - to_uint z{m}))
                    * 2 ^ (to_uint z{m} - to_uint layer{m})
                + 24 * (to_uint node0
                        - to_uint i{m} * 2 ^ (to_uint z{m} - to_uint layer{m})) =>
             BArray786408.is_init_cell b_flat_tree0 i0 by assumption.
      have hfa0 : forall (x : int), 0 <= x < to_uint layer{m} =>
             forall (i0 : int),
               24 * (32768 - 2 ^ (15 - x))
             + 24 * (to_uint i{m} %% 2 ^ (14 - to_uint z{m}))
                 * 2 ^ (to_uint z{m} - x) <= i0 =>
               i0 < 24 * (32768 - 2 ^ (15 - x))
                  + 24 * (to_uint i{m} %% 2 ^ (14 - to_uint z{m}))
                      * 2 ^ (to_uint z{m} - x)
                  + 24 * 2 ^ (to_uint z{m} - x) =>
               BArray786408.is_init_cell b_flat_tree0 i0 by assumption.
      have hEa : 16 - (to_uint layer{m} + 1) = 15 - to_uint layer{m} by ring.
      have hEb : to_uint z{m} - (to_uint layer{m} + 1) + 1
               = to_uint z{m} - to_uint layer{m} by ring.
      rewrite hl1 hEa hEb.
      split. smt().
      split.
      + rewrite hnaeq hnode0; ring.
      move => x hx1 hx2 i0 ha hb.
      case (x < to_uint layer{m}) => hcx.
      + apply (hfa0 x); smt().
      have hxe : x = to_uint layer{m} by smt().
      move: ha hb. rewrite hxe => ha hb.
      apply hpart0; smt().
    auto .
    unroll 9.
    sp. if.
    + seq 2: (0 < to_uint node /\ layer = zero /\ 0 <= to_uint layer /\
              0<= to_uint i < 17 * (JUtils.(`<<`) 1 (14- to_uint z))  /\  to_uint z <= 14 /\
              b_node_addr /\ 0 <= to_uint node_addr <= 786408 - 24 /\
              BArray786408.is_init b_flat_tree (to_uint node_addr) 24 /\
              BArray24.is_init _b_pkseed 0 24 /\ BArray24.is_init _b_skseed 0 24 /\
              to_uint i * 2 ^ (to_uint z - to_uint layer) < to_uint node
                <= (to_uint i + 1) * 2 ^ (to_uint z - to_uint layer) /\
              to_uint rightmost = (to_uint i + 1) * 2 ^ (to_uint z - to_uint layer) /\
              to_uint node_addr =
                24 * (32768 - 2 ^ (15 - to_uint layer))
              + 24 * (to_uint i %% 2 ^ (14 - to_uint z)) * 2 ^ (to_uint z - to_uint layer)
              + 24 * (to_uint node - to_uint i * 2 ^ (to_uint z - to_uint layer))
              - 24 /\
              BArray786408.is_init b_flat_tree
                (  24 * (32768 - 2 ^ (15 - to_uint layer))
                 + 24 * (to_uint i %% 2 ^ (14 - to_uint z)) * 2 ^ (to_uint z - to_uint layer))
                (24 * (to_uint node - to_uint i * 2 ^ (to_uint z - to_uint layer)))).
      + auto.
        if. auto.
        + ecall (__F_proof param_12 b_param_1 param_11 (BArray24.init_arr
                    (W8.of_int 255)) param_10 (BArray32.init_arr (W8.of_int 255))).
          auto .
          ecall (__fors_skgen_proof param_9 b_param_2 param_8 (BArray24.init_arr
                                                    (W8.of_int 255)) 
                param_7 (BArray24.init_arr (W8.of_int 255)) param_6 (BArray32.init_arr
                                                           (W8.of_int 255)) param_5).
          auto .
          ecall (__forest_label_proof param_4 param_3).
          auto .
          ecall (__adrs_set_tree_index_proof param_2 (BArray32.init_arr (W8.of_int 255)
                                           ) param_1).
          auto .
          ecall (__adrs_set_tree_height_proof param_0 (BArray32.init_arr
                                            (W8.of_int 255)) param).
          auto .
          rewrite /is_init /valid /= => /> &m pow 3?.
          rewrite !uleE !ultE /JUtils.(`<<`) /= => 2? i *.
          have: 2^(14 - to_uint _z) <= 2^14. apply StdOrder.IntOrder.ler_weexpn2l. by auto. smt().
          have: 0<= 2^(14-to_uint _z).  rewrite StdOrder.IntOrder.expr_ge0 /=. by auto.
          move => /= 2?.
          move: i. rewrite to_uintK_small /=. 
          + have H: (0 <= to_uint (of_int 14 - _z)). smt(W32.to_uint_cmp).
            rewrite H to_uintB /=. rewrite uleE /=. smt().
            smt(). move => i.
          have hz9 : 0 <= to_uint _z <= 14 by smt(W32.to_uint_cmp).
          have he9 : to_uint (W32.of_int 14 - _z) = 14 - to_uint _z.
          + rewrite W32.to_uintB /=. rewrite uleE /=; smt(). done.
          have hI : to_uint _i < 17 * 2 ^ (14 - to_uint _z).
          + move: i. rewrite he9 /=; smt().
          have hs : (SHL_64 W64.one (truncateu8 _z)).`6 = W64.of_int (2 ^ to_uint _z).
          + apply (shl64_val _z); smt().
          have hpw : pow{m} = W64.of_int (2 ^ to_uint _z).
          + move: pow. rewrite subr0; smt().
          have hpz : 1 <= 2 ^ to_uint _z <= 16384
            by smt(pow2_leA StdOrder.IntOrder.exprn_ege1).
          have htp : truncateu32 pow{m} = W32.of_int (2 ^ to_uint _z).
          + rewrite hpw. apply W32.to_uint_eq.
            rewrite to_uint_truncateu32 W32.of_uintK W64.of_uintK; smt().
          have hsp : 2 ^ (14 - to_uint _z) * 2 ^ to_uint _z = 2 ^ 14.
          + rewrite -pow2_split 1,2:/#.
            by have -> : 14 - to_uint _z + to_uint _z = 14 by ring.
          have hb : 2 ^ to_uint _z * to_uint _i < 278528.
          + have h1 : 2 ^ to_uint _z * to_uint _i
                    < 2 ^ to_uint _z * (17 * 2 ^ (14 - to_uint _z)).
            + apply StdOrder.IntOrder.ltr_pmul2l; smt(StdOrder.IntOrder.expr_gt0).
            smt(pow2_A).
          have hni : to_uint (truncateu32 pow{m} * _i) = 2 ^ to_uint _z * to_uint _i.
          + rewrite htp to_uintM_small W32.of_uintK; smt().
          split. smt(BArray32.init_arrP BArray24.init_arrP).  move => /> *. 
          split. smt(W32.to_uint_cmp).
          move => 2?.
          move => result2 hlo2 hhi2 hv2.
          have hR2 : 0 <= to_uint result2 <= 32766.
          + move: hlo2 hhi2. rewrite !uleE /=. smt(W64.to_uint_cmp).
          have hv2' : to_uint result2 = to_uint (truncateu32 pow{m} * _i) %% 16384.
          + apply (forest_label_val0 result2 (truncateu32 pow{m} * _i)); smt().
          have hmod0 := fors_node_mod (to_uint (truncateu32 pow{m} * _i)) (to_uint _i)
                                      (to_uint _z) 0 _ _ _ _ _.
          + smt().
          + smt().
          + smt().
          + smt().
          + smt().
          have hval2 : to_uint result2
                     = (to_uint _i %% 2 ^ (14 - to_uint _z)) * 2 ^ to_uint _z.
          + move: hmod0. rewrite hni /=; smt(pow2_A).
          have hM2 : to_uint (result2 * (W64.of_int 24)) = to_uint result2 * 24.
          + rewrite to_uintM_small /=; smt().
          split. rewrite to_uintM_small /=; smt(W32.to_uint_cmp).
          move => 2?.
        split; 1: smt(BArray24.init_arrP).
        move => _ result3 ?.
          split.
          + move => i0 hka hkb.
            rewrite SBArray786408_24.SBArray786408_24.is_init_cell_get 1,2:/#.
                       rewrite SBArray786408_24.SBArray786408_24.is_init_cell_set.
                     have : (to_uint (result2 * of_int 24) <= to_uint (result2 * of_int 24) + i0 <
   24 + to_uint (result2 * of_int 24) /\
   0 <= to_uint (result2 * of_int 24) + i0 < 786408) = true.
                       smt().
                     move => temp.
                       rewrite temp.
                       simplify.
                     smt(BArray32.init_arrP BArray24.init_arrP).
          move => ? result4 ?.
          have hnd1 : to_uint (truncateu32 pow{m} * _i + W32.one)
                    = 2 ^ to_uint _z * to_uint _i + 1.
          + rewrite to_uintD_small hni /=; smt().
          have hrm : to_uint (truncateu32 pow{m} + truncateu32 pow{m} * _i)
                   = (to_uint _i + 1) * 2 ^ to_uint _z.
          + rewrite to_uintD_small hni htp W32.of_uintK; smt().
          have hA2 : to_uint (result2 * (W64.of_int 24))
                   = 24 * (to_uint _i %% 2 ^ (14 - to_uint _z)) * 2 ^ to_uint _z.
          + rewrite hM2 hval2; ring.
          split. smt().
          split. smt().
          split. smt().
          split.
          + move => i0 hka hkb.
            rewrite SBArray786408_24.SBArray786408_24.is_init_cell_set.
            smt(BArray32.init_arrP BArray24.init_arrP).
          split. smt().
          split. smt().
          split.
          + rewrite hA2 hnd1; ring.
          move => i0 hka hkb.
                     rewrite SBArray786408_24.SBArray786408_24.is_init_cell_set.
                   have : (to_uint (result2 * of_int 24) <= i0 < 24 + to_uint (result2 * of_int 24) /\
                     0 <= i0 < 786408) = true.
                     smt().
                   move => temp.
                     rewrite temp.
                   simplify.
          smt(BArray32.init_arrP BArray24.init_arrP).
        auto. 
        ecall (__H_proof param_29 b_param_3 param_28 (BArray24.init_arr
               (W8.of_int 255)) param_27 (BArray32.init_arr (W8.of_int 255)) param_26
               (BArray24.init_arr (W8.of_int 255)) param_25 (BArray24.init_arr (W8.of_int 255))).
        auto .
        ecall (__forest_label_proof param_24 param_23).
        auto .
        ecall (__adrs_set_tree_index_proof param_22 (BArray32.init_arr
                                            (W8.of_int 255)) param_21).
        auto .
        ecall (__adrs_set_tree_height_proof param_20 (BArray32.init_arr
                                             (W8.of_int 255)) param_19).
        auto .
        ecall (__copy_nbytes_proof param_18 b_param_5 param_17 b_param_4).
        auto .
        ecall (__copy_nbytes_proof param_16 b_param_7 param_15 b_param_6).
        auto .
        ecall (__forest_label_proof param_14 param_13).
        auto .
        while(layer = zero /\ 0<= to_uint i < 17 * (JUtils.(`<<`) 1 (14- to_uint z)) /\
              to_uint z <= 14 /\ b_node_addr /\ 0 <= to_uint node_addr <= 786408 - 24 /\
              BArray786408.is_init b_flat_tree (to_uint node_addr) 24 /\
              BArray24.is_init _b_pkseed 0 24 /\ BArray24.is_init _b_skseed 0 24 /\
              to_uint i * 2 ^ (to_uint z - to_uint layer) < to_uint node
                <= (to_uint i + 1) * 2 ^ (to_uint z - to_uint layer) /\
              to_uint rightmost = (to_uint i + 1) * 2 ^ (to_uint z - to_uint layer) /\
              to_uint node_addr =
                24 * (32768 - 2 ^ (15 - to_uint layer))
              + 24 * (to_uint i %% 2 ^ (14 - to_uint z)) * 2 ^ (to_uint z - to_uint layer)
              + 24 * (to_uint node - to_uint i * 2 ^ (to_uint z - to_uint layer))
              - 24 /\
              BArray786408.is_init b_flat_tree
                (  24 * (32768 - 2 ^ (15 - to_uint layer))
                 + 24 * (to_uint i %% 2 ^ (14 - to_uint z)) * 2 ^ (to_uint z - to_uint layer))
                (24 * (to_uint node - to_uint i * 2 ^ (to_uint z - to_uint layer)))).
        + auto. if.
          + auto. 
            ecall (__F_proof param_12 b_param_1 param_11 (BArray24.init_arr
                    (W8.of_int 255)) param_10 (BArray32.init_arr (W8.of_int 255))).
            auto .
            ecall (__fors_skgen_proof param_9 b_param_2 param_8 (BArray24.init_arr
                                                    (W8.of_int 255)) 
                param_7 (BArray24.init_arr (W8.of_int 255)) param_6 (BArray32.init_arr
                                                           (W8.of_int 255)) param_5).
            auto .
            ecall (__forest_label_proof param_4 param_3).
            auto .
            ecall (__adrs_set_tree_index_proof param_2 (BArray32.init_arr (W8.of_int 255)
                                           ) param_1).
            auto .
            ecall (__adrs_set_tree_height_proof param_0 (BArray32.init_arr
                                            (W8.of_int 255)) param).
            auto .
            rewrite /is_init /valid /= => /> &m 4?.  rewrite !ultE /= => *. 
            split. smt(BArray32.init_arrP BArray24.init_arrP).
            move => ? result0 ? result1 ?.
            have hz9 : 0 <= to_uint z{m} <= 14 by smt(W32.to_uint_cmp).
            have hpz : 1 <= 2 ^ to_uint z{m} <= 16384
              by smt(pow2_leA StdOrder.IntOrder.exprn_ege1).
            have hI : to_uint i{m} < 17 * 2 ^ (14 - to_uint z{m}).
            + rewrite -shl1 1:/#; smt().
            have hsp : 2 ^ (14 - to_uint z{m}) * 2 ^ to_uint z{m} = 2 ^ 14.
            + rewrite -pow2_split 1,2:/#.
              by have -> : 14 - to_uint z{m} + to_uint z{m} = 14 by ring.
            have hi1 : (to_uint i{m} + 1) * 2 ^ to_uint z{m} <= 278528.
            + have h1 : (to_uint i{m} + 1) * 2 ^ to_uint z{m}
                      <= (17 * 2 ^ (14 - to_uint z{m})) * 2 ^ to_uint z{m}.
              + apply StdOrder.IntOrder.ler_wpmul2r; smt(StdOrder.IntOrder.expr_ge0).
              smt(pow2_A).
            have hPart0 : forall (i0 : int),
                   24 * (to_uint i{m} %% 2 ^ (14 - to_uint z{m})) * 2 ^ to_uint z{m} <= i0 =>
                   i0 < 24 * (to_uint i{m} %% 2 ^ (14 - to_uint z{m})) * 2 ^ to_uint z{m}
                      + 24 * (to_uint node{m} - to_uint i{m} * 2 ^ to_uint z{m}) =>
                   BArray786408.is_init_cell b_flat_tree{m} i0 by assumption.
            split.
            + split.
              + rewrite W32.uleE; smt(W32.to_uint_cmp W32.of_uintK).
              rewrite shl1 1:// pow2_A W32.of_uintK /=; smt().
            move => 2? result2 hpnz2 hlo2 hhi2 hv2 hv2'.
            have hR2 : 0 <= to_uint result2 <= 32766.
            + move: hlo2 hhi2. rewrite !uleE /=. smt(W64.to_uint_cmp).
            have hv2i : to_uint result2 = to_uint node{m} %% 16384.
            + apply (forest_label_val0 result2 node{m}). smt().
              move: hv2. by rewrite shl1 1:// pow2_A.
            have hmod0 := fors_node_mod (to_uint node{m}) (to_uint i{m}) (to_uint z{m}) 0
                            _ _ _ _ _.
            + smt().
            + smt().
            + smt().
            + smt().
            + smt().
            have hval2 : to_uint result2
                       = (to_uint i{m} %% 2 ^ (14 - to_uint z{m})) * 2 ^ to_uint z{m}
                       + (to_uint node{m} - to_uint i{m} * 2 ^ to_uint z{m}).
            + move: hmod0. rewrite /=; smt(pow2_A).
            have hM2 : to_uint (result2 * (W64.of_int 24)) = to_uint result2 * 24.
            + rewrite to_uintM_small /=; smt().
            have hnd1 : to_uint (node{m} + W32.one) = to_uint node{m} + 1.
            + rewrite to_uintD_small /=; smt().
            split. smt().
            move => 2?.
        split; 1: smt(BArray24.init_arrP).
        move => _ result3 ?.
            split.
            + move => i0 hka hkb.
              have hs2 : 0 <= to_uint (result2 * (W64.of_int 24)) + i0 < 786408.
              + rewrite hM2; smt().
              rewrite SBArray786408_24.SBArray786408_24.is_init_cell_get 1,2:/#.
              rewrite SBArray786408_24.SBArray786408_24.is_init_cell_set.
              smt(BArray32.init_arrP BArray24.init_arrP).
            move => ? result4 ?.
            split. smt().
            split.
            + move => i0 hka hkb.
              have hA3 : 0 <= to_uint (result2 * (W64.of_int 24)) <= 786384.
              + rewrite hM2; smt().
              rewrite SBArray786408_24.SBArray786408_24.is_init_cell_set.
              case (to_uint (result2 * (W64.of_int 24)) <= i0 <
                    24 + to_uint (result2 * (W64.of_int 24)) /\ 0 <= i0 < 786408) => hc /=.
              + smt(BArray32.init_arrP BArray24.init_arrP).
              smt().
            split. smt().
            split.
            + rewrite hM2 hval2 hnd1; ring.
            move => i0 hka hkb.
            have hA4 : 0 <= to_uint (result2 * (W64.of_int 24)) <= 786384.
            + rewrite hM2; smt().
            rewrite !SBArray786408_24.SBArray786408_24.is_init_cell_set.
            case (to_uint (result2 * (W64.of_int 24)) <= i0 <
                  24 + to_uint (result2 * (W64.of_int 24)) /\ 0 <= i0 < 786408) => hc /=.
            + smt(BArray32.init_arrP BArray24.init_arrP).
            apply hPart0; smt().
          exfalso. smt().
        auto. rewrite /is_init /=.  move => &m /> *.
        split.
        + split. smt(W32.to_uint_cmp).
          split. smt(W32.ultE W32.to_uint_cmp).
          move => x hx1 hx2 i0 ha hb.
          have hx0 : x = 0 by smt().
          move: ha hb. rewrite hx0 pow2_A1 /= => ha hb.
          smt(W32.ultE W32.to_uint_cmp).
        smt(SBArray786408_24.SBArray786408_24.is_init_cell_get BArray32.init_arrP BArray24.init_arrP).
      exfalso. move => &m />.  rewrite !ultE !uleE negb_and /=.
      case(to_uint node{m} < to_uint rightmost{m}). by auto.
      move => H /=. rewrite !negb_and /=.
      rewrite -!implybE /= => exp pow node rightmost. rewrite orbC -!implybE /= => 5? layer. 
      rewrite orbA orbC -implybE /= => ?. rewrite orbA orbC -implybE /= => i.
      do 3! rewrite orbA orbC -implybE /= => *.
      left. move => *. move : H.  
      rewrite rightmost !node /=.
      have HE: 0 <= to_uint exp{m} <= 14. move: exp. rewrite layer subr0 /=. smt().
      have HP: 1 <= to_uint pow{m} <=16384.
      + move: pow. rewrite /SHL_64 /W64.shift_mask /flags_w /rflags_OF to_uint_truncateu8 /=.
        have exp_mod: to_uint exp{!m} %% 256 %% 64 = to_uint exp{!m}. smt(). rewrite !exp_mod /=.
        case(to_uint exp{m} = 0). move => * /= .
        + have: pow{m} = one. smt(). rewrite to_uint_eq /=. smt().
        move => * /=. have: pow{m} = one `<<<` to_uint exp{!m}.  smt().
        rewrite shlMP /=. smt().
        have: 2 ^ to_uint exp{!m} <= 2 ^ 14. by apply StdOrder.IntOrder.ler_weexpn2l.
        move => /= Hpow pow. rewrite pow /=. rewrite to_uintK_small /=. rewrite StdOrder.IntOrder.expr_ge0 /=.  by auto. smt(). rewrite StdOrder.IntOrder.exprn_ege1. smt(). by auto. smt().
    have HI: 0 <= to_uint i{m} <= 17 *  16384. move: i. rewrite /JUtils.(`<<`) /=.
    + have: 0 <= ( 14 - to_uint _z) <= 14. smt().
      have: 2^(14 - to_uint _z) <= 2^14.  apply StdOrder.IntOrder.ler_weexpn2l. by auto. smt(). 
      have: 0<= 2^(14 - to_uint _z).  rewrite StdOrder.IntOrder.expr_ge0 /=. by auto.
      move => /= 3?. rewrite to_uintK_small to_uintB /=. rewrite uleE /=. smt(). smt().
      + rewrite uleE /=. smt().
      smt().                         
    move: i => hIi.
have hez : to_uint exp{m} = to_uint z{m} by rewrite exp layer subr0.
have hs := shl64_val exp{m} (to_uint exp{m}) _ _; 1,2: smt().
have hpv : pow{m} = W64.of_int (2 ^ to_uint exp{m}) by rewrite -hs -pow.
have hz14 : to_uint (W32.of_int 14 - _z) = 14 - to_uint _z.
  by rewrite W32.to_uintB /= 1:uleE /=; smt().
have hiz : to_uint i{m} < 17 * 2 ^ (14 - to_uint z{m}).
have hbz : 0 <= 17 * 2 ^ (14 - to_uint z{m}) <= 17 * 16384.
  have := pow2_leA (14 - to_uint z{m}) _; 1: smt(W32.to_uint_cmp).
  smt(StdOrder.IntOrder.expr_ge0).
move: hIi; rewrite hz14 shl1 1:/# W32.of_uintK IntDiv.modz_small 1:/#.
smt().
have hpz : to_uint (truncateu32 pow{m}) = 2 ^ to_uint z{m}.
  rewrite hpv to_uint_truncateu32 W64.of_uintK hez.
  have := pow2_leA (to_uint z{m}) _; 1: smt(W32.to_uint_cmp).
  smt(IntDiv.modz_small StdOrder.IntOrder.expr_gt0).
have hsp : 2 ^ to_uint z{m} * 2 ^ (14 - to_uint z{m}) = 2 ^ 14.
  have hz0 := W32.to_uint_cmp z{m}.
  by rewrite -pow2_split 1,2:/#; congr; ring.
have hprod : 2 ^ to_uint z{m} * to_uint i{m} < 17 * 2 ^ 14.
  have h1 : 2 ^ to_uint z{m} * to_uint i{m} < 2 ^ to_uint z{m} * (17 * 2 ^ (14 - to_uint z{m})).
    rewrite StdOrder.IntOrder.ltr_pmul2l; smt(StdOrder.IntOrder.expr_gt0).
  have h2 : 2 ^ to_uint z{m} * (17 * 2 ^ (14 - to_uint z{m})) = 17 * 2 ^ 14 by rewrite -hsp; ring.
  by rewrite -h2; exact h1.
have hA14 : 2 ^ 14 = 16384 by rewrite pow2_A.
rewrite to_uintD_small !to_uintM_small hpz; smt(W32.to_uint_cmp).
  exfalso. move => &m /> /= *. rewrite !uleE /=.
  case (layer{m} = zero). move => *.
  have H: layer{m} = zero => to_uint layer{m} = 0. by auto.
  rewrite H; smt().
  by auto. 
qed.

lemma __fors_node_proof _root _b_root _skseed _b_skseed _i _z _pkseed _b_pkseed _adrs _b_adrs :
      (__fors_node_spec _root _b_root _skseed _b_skseed _i _z _pkseed
      _b_pkseed _adrs _b_adrs).
proof.
rewrite /__fors_node_spec .
proc; auto .
ecall (fors_node_proof param_4 b_param param_3 (BArray24.init_arr
                                               (JWord.W8.of_int 255)) param_2 
       param_1 param_0 (BArray24.init_arr (JWord.W8.of_int 255)) param (
                                                                 BArray32.init_arr
                                                                 (JWord.W8.of_int
                                                                 255))).
auto .
smt(BArray32.init_arrP BArray24.init_arrP).
qed .

lemma fors_sign_proof _sig_fors _b_sig_fors _md _b_md _skseed _b_skseed _pkseed _b_pkseed _adrs _b_adrs :
      (fors_sign_spec _sig_fors _b_sig_fors _md _b_md _skseed _b_skseed
      _pkseed _b_pkseed _adrs _b_adrs).
proof.
rewrite /fors_sign_spec .
  proc; auto .

                                                                   have : forall (x : JWord.W32.t), (JWord.W32."_.[_]" x 0 = true) => (JWord.W32."_.[_]" ((JWord.W32.(`^`)) x JWord.W32.one) 0 = false).


                      smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                             move => xor_one_lbt.

                                                               have : forall (x : JWord.W32.t), (JWord.W32."_.[_]" x 0 = false) => (JWord.W32."_.[_]" ((JWord.W32.(`^`)) x JWord.W32.one) 0 = true).
                                                                   smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                             move => xor_one_lbf.


          have xor_same_g0 : forall (x : JWord.W32.t) (i : int), i <> 0 => 
        JWord.W32."_.[_]"(JWord.W32.(`^`) x JWord.W32.one) i = JWord.W32."_.[_]" x i.
                                                                   smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                          
                                                               have : forall (w : JWord.W32.t), (JWord.W32."_.[_]" w 0 = true) => (JWord.W32.(`&`) w (JWord.W32.masklsb 1)) = JWord.W32.one.
                                                             move => w.
                                                             move => aux.
                                                               have := JWord.W32.wordP (JWord.W32.(`&`) w (JWord.W32.masklsb 1)) JWord.W32.one.

                                                             move => aux2.
                                                               apply aux2.
                                                             move => aux3 aux4.

                                                               have := JWord.W32.andwE w (JWord.W32.masklsb 1) aux3.
                                                             move => aux5.
                                                               rewrite aux5.
                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                             move => one_and_one_eq_one.

                                                                                                                            have : forall (w : JWord.W32.t), (JWord.W32."_.[_]" w 0 = false) => (JWord.W32.(`&`) w (JWord.W32.masklsb 1)) = JWord.W32.zero.
                                                             move => w.
                                                             move => aux.
                                                               have := JWord.W32.wordP (JWord.W32.(`&`) w (JWord.W32.masklsb 1)) JWord.W32.zero.

                                                             move => aux2.
                                                               apply aux2.
                                                             move => aux3 aux4.

                                                               have := JWord.W32.andwE w (JWord.W32.masklsb 1) aux3.
                                                             move => aux5.
                                                               rewrite aux5.
                                                                                                                            smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                             move => zero_and_one_eq_zero.

                                                               have : forall (x : JWord.W32.t), (JWord.W32.(`>>>`) x 1) = (JWord.W32.(`>>>`) ((JWord.W32.(`^`) x JWord.W32.one)) 1).
                                                             move => w.

                                                               have := JWord.W32.wordP (JWord.W32.(`>>>`) w 1) (JWord.W32.(`>>>`) (JWord.W32.(`^`) w JWord.W32.one) 1).
                                                             move => aux.
                                                               apply aux.
                                                             move => aux2 aux3.

                                                               have := JWord.W32.shrwE w 1 aux2.
                                                             move => aux4.
                   have := JWord.W32.shrwE ((JWord.W32.(`^`) w JWord.W32.one)) 1 aux2.
                                                             move => aux5.

                                                               have : ((0 <= aux2 < 32 && JWord.W32."_.[_]" w (aux2 + 1))) = (0 <= aux2 < 32 && JWord.W32."_.[_]" (JWord.W32.(`^`) w JWord.W32.one) (aux2 + 1)).

                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                             move => aux6.
                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                             move => shift_xor_eq.

                                                             have : forall (x : JWord.W32.t),
           JWord.W32.to_uint (JWord.W32.(`>>>`) x 1) =
                                                               JWord.W32.to_uint (JWord.W32.(`>>>`) (JWord.W32.(`^`) x JWord.W32.one) 1).
                                                                                  smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
                                                               BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg JWord.W32.xorwE JWord.W32.get_to_uint).
                                                             move => shift_xor_eq_uint.
                                                             
                 have : forall (x : JWord.W32.t),
           JWord.W32.to_uint x %/ 2 ^ 1 =
                                                               JWord.W32.to_uint (JWord.W32.(`^`) x JWord.W32.one) %/ 2 ^ 1.
                                                             move => w.
                                                               have := JWord.W32.to_uint_shr w 1.
                                                             move => part1.

                                                               have := JWord.W32.to_uint_shr ((JWord.W32.(`^`) w JWord.W32.one)) 1.
                                                             move => part2.

                                                               have := shift_xor_eq_uint w.
                                                               rewrite part1.
                                                               smt().
                                                               rewrite part2.
                                                               smt().
                                                               smt().
                                                             simplify.
                                                             
                                                             move => div2_xor_eq.
                                                            

          have : forall (x : JWord.W32.t), JWord.W32.to_uint ((JWord.W32.(`^`)) x JWord.W32.one) <=
                                                             (JWord.W32.to_uint x) + 1.
                                                             move => w.

                                                               case : (JWord.W32."_.[_]" w 0 = true).
                                                             move => case1.

                                                               have := JWord.W32.splitwE 1 ((JWord.W32.(`^`) w JWord.W32.one)).
                                                             move => aux.

                                                               have := zero_and_one_eq_zero ((JWord.W32.(`^`) w JWord.W32.one)).
                                                             move => aux2.
                                                               move : aux.
                                                               rewrite aux2.
                                                               have :=  xor_one_lbt.
                                                             move => aux3.
                                                               have :  (JWord.W32."_.[_]" (JWord.W32.(`^`) w JWord.W32.one) 0 = false).
                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                               smt().

                                                               have := JWord.W32.to_uint_shr ((JWord.W32.(`^`) w JWord.W32.one)) 1.
                                                             move => aux3.
                                                               rewrite aux3.
                                                               smt().
                                                               simplify.

                      have : (2 * (JWord.W32.to_uint (JWord.W32.(`^`) w JWord.W32.one) %/ 2)) <= (JWord.W32.to_uint (JWord.W32.(`^`) w JWord.W32.one)).
                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                             move => aux4.
                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                             move => case2.

                                                                                                                            have := JWord.W32.splitwE 1 ((JWord.W32.(`^`) w JWord.W32.one)).
                                                             move => aux.

                                                               have := one_and_one_eq_one ((JWord.W32.(`^`) w JWord.W32.one)).
                                                             move => aux2.
                                                               move : aux.
                                                               rewrite aux2.
                                                               have := xor_one_lbt w.
                                                             move => aux3.
                                                               have :  (JWord.W32."_.[_]" (JWord.W32.(`^`) w JWord.W32.one) 0 = true).
                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                               smt().

                                                               have := JWord.W32.to_uint_shr ((JWord.W32.(`^`) w JWord.W32.one)) 1.
                                                             move => aux3.
                                                               rewrite aux3.
                                                               smt().
                                                               simplify.

                      have : (2 * (JWord.W32.to_uint (JWord.W32.(`^`) w JWord.W32.one) %/ 2)) <= (JWord.W32.to_uint (JWord.W32.(`^`) w JWord.W32.one)).
                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                             move => aux4.
                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                             move => xor_one_bound.
                               have : forall (x : JWord.W32.t),
                                                               JWord.W32."_.[_]" x 0 = true => Int.odd (JWord.W32.to_uint x).

                                                             move => x hbit0.
have h := JWord.W32.get_to_uint x 0.
                                                               rewrite hbit0 in h.
                                                               move : h.
                                                             simplify.
                                                               smt(IntDiv.oddP).
                                                             move => lbt_odd.
                                                             

                              have : forall (x : JWord.W32.t),
                                                               JWord.W32."_.[_]" x 0 = false => !Int.odd (JWord.W32.to_uint x).

                                                             move => x hbit0.
have h := JWord.W32.get_to_uint x 0.
                                                               rewrite hbit0 in h.
                                                               move : h.
                                                             simplify.
                                                               smt(IntDiv.oddP).
                                                             move => lbf_nodd.

                                                               have : forall (x : JWord.W32.t) (i : int),
                                                             (JWord.W32.to_uint x <= i /\ Int.odd i /\ !Int.odd (JWord.W32.to_uint x)) =>
                                                             (JWord.W32.to_uint x <= i - 1).

                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one IntDiv.divzMDl IntDiv.oddW IntDiv.oddP).
                                                             move => nodd_odd_tight_bound.

                               
                                                                                                                

                                                               have : forall (n : int), Int.odd n => n %/ 2 = (n-1) %/ 2.
                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one IntDiv.divzMDl IntDiv.oddW).
                                                             move => odd_div2.

                                                               have :  forall (n x : int), (2 <= x) => n %/ (2 ^ x) = ((n %/ 2) %/ (2 ^ (x - 1))).

                                                             move => n x hx.
have hexp : 2 ^ x = 2 * 2 ^ (x-1).
  smt( StdOrder.IntOrder.Domain.exprS).
have h2pos : 0 < 2^(x-1) by smt(StdOrder.IntOrder.expr_gt0).
                                                               smt(IntDiv.divz_mulp).
                                                             move => exp_div_split.

                                                                               have :  forall (n x : int), (2 <= x) => n %/ (2 ^ x) = (((n %/ (2 ^ (x - 1))) %/ 2)).

                                                             move => n x hx.
have hexp : 2 ^ x = 2 * 2 ^ (x-1).
  smt( StdOrder.IntOrder.Domain.exprS).
have h2pos : 0 < 2^(x-1) by smt(StdOrder.IntOrder.expr_gt0).
                                                               smt(IntDiv.divz_mulp).
                                                             move => exp_div_split2.

                                                               have : forall (n x : int), (Int.odd n /\ 2 <= x) => n %/ (2 ^ x) = (n-1) %/ (2 ^ x).
                                                             move => n x idk.

                                                               have := exp_div_split n x.
                                                             move => aux.
                                                               rewrite aux.
                                                               smt().
                                                               have := odd_div2 n.
                                                             move => aux2.
                                                               rewrite aux2.
                                                             smt().

                           
                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one IntDiv.divzMDl IntDiv.oddW).
                                                             move => odd_div_exp.

   have : forall (x : JWord.W32.t), (JWord.W32."_.[_]" x 0 = true)  =>
                JWord.W32.to_uint((JWord.W32.(`^`) x JWord.W32.one)) = (JWord.W32.to_uint x) - 1.
                                                             move => w.

                                                               have := JWord.W32.splitwE 1 ((JWord.W32.(`^`) w JWord.W32.one)).
                                                             move => aux.
                                                               rewrite aux.
                                                               smt().
                                                             move => aux2.
                                                               have := zero_and_one_eq_zero ((JWord.W32.(`^`) w JWord.W32.one)).
                                                             move => aux3.
                                                               have := xor_one_lbt w.
                                                             move => aux4.
                                                             
                                                               rewrite aux3.
                                                             

                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one IntDiv.divzMDl IntDiv.oddW IntDiv.oddP).

                                                               have := shift_xor_eq_uint w.
                                                             move => aux5.
                                                               rewrite -aux5.
                                                               have := JWord.W32.to_uint_shr w 1.
                                                             move => aux6.
                                                               rewrite aux6.
                                                               smt().
                                                             
                                                               smt( Bool.xorK JWord.W32.xorwE JWord.W32.nth_one).
                                                             move => lbt_xor_minus_one.

while ((JWord.W64.(\ule) JWord.W64.zero i) /\
      (JWord.W64.(\ule) i (JWord.W64.of_int 17)) /\
      (JWord.W64.to_uint offset = (JWord.W64.to_uint i) * 15 * 24) /\
      (forall (k : int), ((0 <= k /\ k < 17) =>
      (JWord.W32.to_uint (BArray68.get32d indices (4 * k)) < 16384))) /\
      (BArray6120.is_init b_sig_fors 0 (JWord.W64.to_uint offset)) /\
      (BArray68.is_init b_indices 0 68)).
auto .
while ((JWord.W32.(\ule) JWord.W32.zero j) /\
      (JWord.W32.(\ule)) j (JWord.W32.of_int 14) /\
      (JWord.W64.(\ule) JWord.W64.zero i) /\
      (JWord.W64.(\ult) i (JWord.W64.of_int 17)) /\
      (forall (k : int), ((0 <= k /\ k < 17) =>
      (JWord.W32.to_uint (BArray68.get32d indices (4 * k)) < 16384))) /\
      (s = JWord.W32.(`^`) (JWord.W32.of_int(JWord.W32.to_uint((BArray68.get32d indices
      (4 * JWord.W64.to_uint i))) %/ (2 ^ (JWord.W32.to_uint j)))) JWord.W32.one) /\
      (JWord.W64.to_uint offset = (JWord.W64.to_uint i) * 15 * 24 + (JWord.W32.to_uint j + 1) * 24) /\
      (BArray6120.is_init b_sig_fors 0 (JWord.W64.to_uint offset))).
auto .
ecall (__fors_node_proof param_11 b_param param_10 (BArray24.init_arr
                                                   (JWord.W8.of_int 255)) param_9 
       param_8 param_7 (BArray24.init_arr (JWord.W8.of_int 255)) param_6 (
                                                                   BArray32.init_arr
                                                                   (JWord.W8.of_int
                                                                   255))).
auto .
                                                                     rewrite /is_init /valid /=.
                                                                     progress.
                                                                     smt(JWord.W64.to_uint_cmp).
                                                                     smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
                                                                     smt(BArray32.init_arrP BArray24.init_arrP).
                                                                     smt(BArray32.init_arrP BArray24.init_arrP).
                                                                     smt(BArray32.init_arrP BArray24.init_arrP).
                                                                     smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
                                                                     rewrite /JWord.W64.SHIFT.SHL_64.
                                                                     simplify.

                                                               have : (JWord.W64.shift_mask
              (JWord.W4u8.truncateu8
                 (JWord.W32.WRingA.(-) (JWord.W32.of_int 14) j{hr})) =
            0) = false.
                                                                     rewrite /JWord.W64.shift_mask.
                   simplify.
                   rewrite /JWord.W4u8.truncateu8.
                   rewrite /JWord.W32.(+).
                   rewrite /JWord.W32.ulift2.
                   rewrite /JWord.W32.([-]).
                   rewrite /JWord.W32.ulift1.
                   rewrite JWord.W8.of_uintK.
                   move : H6.
                   rewrite /JWord.W32.(\ult).
                   rewrite JWord.W32.of_uintK.
                   rewrite JWord.W32.of_uintK.
                   rewrite JWord.W32.of_uintK.
                   smt(JWord.W32.to_uint_cmp).

             move => aux.
                   rewrite aux.
                   simplify.
                   rewrite /JWord.W64.SHIFT.rflags_OF.
                   simplify.
                   rewrite /JWord.W2u32.truncateu32.
                   rewrite /JWord.W4u8.truncateu8.
                   rewrite /JWord.W64.shift_mask.
                   simplify.
                   rewrite /JUtils.(`<<`).
             have : (0 <=
                   JWord.W32.to_uint (JWord.W32.WRingA.(-) (JWord.W32.of_int 14) j{hr})) = true.
                   smt(JWord.W32.to_uint_cmp).
             move => aux2.
                   rewrite aux2.
                   simplify.
                   rewrite /JWord.W32.(+).
                   rewrite /JWord.W32.ulift2.
                   rewrite /JWord.W32.([-]).
                   rewrite /JWord.W32.ulift1.
               rewrite JWord.W64.to_uint_shl.
               smt().
               rewrite /JWord.W32.(\ult).
             simplify.
               rewrite JWord.W32.of_uintK.
               rewrite JWord.W32.of_uintK.
               rewrite JWord.W32.of_uintK.
               rewrite JWord.W32.of_uintK.
               rewrite JWord.W32.of_uintK.
               rewrite JWord.W32.of_uintK.
               simplify.

               have : ((14 - JWord.W32.to_uint j{hr}) %% 4294967296 %% 256 %% 64) = ((14 - JWord.W32.to_uint j{hr}) %% 64).
               smt().
             move => temp.
               rewrite temp.
               have : ((14 - JWord.W32.to_uint j{hr}) %% 64) = (14 - JWord.W32.to_uint j{hr}).
               smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
             move => temp2.
               rewrite temp2.
               have := StdOrder.IntOrder.ler_weexpn2l 2 _ (14 - JWord.W32.to_uint j{hr}) 14 _.
               trivial.
               smt(JWord.W32.to_uint_cmp).
             simplify.
             move => aux3.

             have : (JWord.W64.to_uint i{hr} * 2 ^ (14 - JWord.W32.to_uint j{hr}) %%
               18446744073709551616 %% 4294967296) = (JWord.W64.to_uint i{hr} * 2 ^ (14 - JWord.W32.to_uint j{hr})).

               smt(JWord.W32.of_uintK StdOrder.IntOrder.expr_gt0).
             move => temp3.
             rewrite temp3.
             
               have := StdOrder.IntOrder.ler_weexpn2l 2 _ (JWord.W32.to_uint j{hr}) 14 _.
               trivial.
               smt(JWord.W32.to_uint_cmp).
             simplify.
             move => aux4.
             have : ((JWord.W64.to_uint i{hr} * 2 ^ (14 - JWord.W32.to_uint j{hr}) +
 JWord.W32.to_uint
   (JWord.W32.(`^`)
      (JWord.W32.of_int
         (JWord.W32.to_uint
            (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
          2 ^ JWord.W32.to_uint j{hr})) JWord.W32.one)) %%
4294967296) = ((JWord.W64.to_uint i{hr} * 2 ^ (14 - JWord.W32.to_uint j{hr}) +
 JWord.W32.to_uint
   (JWord.W32.(`^`)
      (JWord.W32.of_int
         (JWord.W32.to_uint
            (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
          2 ^ JWord.W32.to_uint j{hr})) JWord.W32.one))).

              smt(JWord.W32.to_uint_cmp JWord.W32.to_uint_small StdOrder.IntOrder.expr_gt0).
  move => aux5.
              rewrite aux5.

              have : ((14 + (- JWord.W32.to_uint j{hr}) %% 4294967296) %% 4294967296) = ((14 + (- JWord.W32.to_uint j{hr})) %% 4294967296).
              smt().
  move => temp4.
              rewrite temp4.

              have : ((14 - JWord.W32.to_uint j{hr}) %% 4294967296) = ((14 - JWord.W32.to_uint j{hr})).
              smt().
  move => temp5.
              rewrite temp5.

              have : (17 * 2 ^ (14 - JWord.W32.to_uint j{hr}) %% 4294967296) = (17 * 2 ^ (14 - JWord.W32.to_uint j{hr})).

              smt(StdOrder.IntOrder.expr_gt0).
  move => temp6.
  rewrite temp6.

  case : (JWord.W32."_.[_]" ((JWord.W32.of_int
        (JWord.W32.to_uint
           (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
             2 ^ JWord.W32.to_uint j{hr}))) 0 = true).
   move => case1.

   have : (JWord.W32.to_uint
  (JWord.W32.(`^`)
     (JWord.W32.of_int
        (JWord.W32.to_uint
           (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
         2 ^ JWord.W32.to_uint j{hr})) JWord.W32.one)) = (JWord.W32.to_uint
  (
     (JWord.W32.of_int
        (JWord.W32.to_uint
           (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
             2 ^ JWord.W32.to_uint j{hr})))) - 1.
             smt().
   move => aux6.
             rewrite aux6.
             rewrite JWord.W32.of_uintK.
             simplify.

have : (JWord.W32.to_uint
   (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
 2 ^ JWord.W32.to_uint j{hr} %% 4294967296) = (JWord.W32.to_uint
   (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
     2 ^ JWord.W32.to_uint j{hr}).

     smt(JWord.W32.to_uint_cmp StdOrder.IntOrder.expr_gt0).
 move => aux7.
     rewrite aux7.

     have : (JWord.W64.to_uint i{hr}) < 17.

     smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
 move => random_bound.


     have : (JWord.W64.to_uint i{hr} * 2 ^ (14 - JWord.W32.to_uint j{hr}) +
(JWord.W32.to_uint
   (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
 2 ^ JWord.W32.to_uint j{hr}) <=
17 * 2 ^ (14 - JWord.W32.to_uint j{hr})
)
 =>
 (JWord.W64.to_uint i{hr} * 2 ^ (14 - JWord.W32.to_uint j{hr}) +
(JWord.W32.to_uint
   (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
 2 ^ JWord.W32.to_uint j{hr} - 1) <
17 * 2 ^ (14 - JWord.W32.to_uint j{hr})
).
    smt().
    apply.

have : (JWord.W32.to_uint
  (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr}))) <= 16383.

    smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
move => random_bound2.

    have : (JWord.W64.to_uint i{hr} * 2 ^ (14 - JWord.W32.to_uint j{hr}) +
((16383) %/
2 ^ JWord.W32.to_uint j{hr}) <= 17 * 2 ^ (14 - JWord.W32.to_uint j{hr})
)
=>
(JWord.W64.to_uint i{hr} * 2 ^ (14 - JWord.W32.to_uint j{hr}) +
JWord.W32.to_uint
  (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
    2 ^ JWord.W32.to_uint j{hr} <= 17 * 2 ^ (14 - JWord.W32.to_uint j{hr})).

    smt(JWord.W32.to_uint_cmp IntDiv.leq_div2r).
    apply.
have := StdOrder.IntOrder.Domain.exprD_nneg 2 ((14 - JWord.W32.to_uint j{hr})) (JWord.W32.to_uint j{hr}).
move => aux9.
have : (0 <= 14 - JWord.W32.to_uint j{hr} =>
           0 <= JWord.W32.to_uint j{hr} =>
           2 ^ (14) =
  2 ^ (14 - JWord.W32.to_uint j{hr}) * 2 ^ JWord.W32.to_uint j{hr}).
  have : (14 - JWord.W32.to_uint j{hr} + JWord.W32.to_uint j{hr}) = 14.
  smt().
move => aux10.
  move : aux9.
rewrite aux10.
  smt().
move => aux10.
    have : (((2 ^ 14) - 1) %/ 2 ^ JWord.W32.to_uint j{hr}) = (((2 ^ 14) %/ 2 ^ JWord.W32.to_uint j{hr}) - 1).
  have : (2 ^ 14) = (2 ^ (14 - JWord.W32.to_uint j{hr})) * (2 ^ JWord.W32.to_uint j{hr}).
apply aux10.
  smt().
  smt(JWord.W32.to_uint_cmp).
move => aux11.

  rewrite aux10.
  smt().
  smt(JWord.W32.to_uint_cmp).
  have := (IntDiv.divzMDl (2 ^ (14 - JWord.W32.to_uint j{hr})) (-1) (2 ^ JWord.W32.to_uint j{hr})).
move => aux12.
  rewrite aux12.
  smt(StdOrder.IntOrder.expr_gt0).
  have := (IntDiv.divzMDl (2 ^ (14 - JWord.W32.to_uint j{hr})) 0 (2 ^ JWord.W32.to_uint j{hr})).
move => aux13.
  rewrite aux13.
  smt(StdOrder.IntOrder.expr_gt0).
  smt(StdOrder.IntOrder.expr_gt0).
move => aux11.

have : 16383 = (2 ^ 14) - 1.
  smt().
move => aux12.
  rewrite aux12.
rewrite aux11.

  have : (2 ^ 14 %/ 2 ^ JWord.W32.to_uint j{hr}) = (2 ^ (14 -JWord.W32.to_uint j{hr})).

have : 2 ^ 14 =
  2 ^ (14 - JWord.W32.to_uint j{hr}) * 2 ^ JWord.W32.to_uint j{hr}.
  apply aux10.
smt().
  smt(JWord.W32.to_uint_cmp).
move => aux13.
rewrite aux13.

      
  smt().
  smt().

move => case2.

     have : (JWord.W64.to_uint i{hr}) < 17.

     smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
 move => random_bound.

have : (JWord.W32.to_uint
  (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr}))) <= 16383.

    smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
move => random_bound2.
    have : (2 ^ 0) = 1.
    smt().
move => aux6.
have : ((JWord.W32.to_uint
           (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
             2 ^ JWord.W32.to_uint j{hr})) <= 16383.
             smt(StdOrder.IntOrder.expr_gt0).
       move => aux7.

       have : !odd(JWord.W32.to_uint(JWord.W32.of_int
        (JWord.W32.to_uint
           (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
             2 ^ JWord.W32.to_uint j{hr}))).
             smt().
     move => aux8.
       
have : (
        (JWord.W32.to_uint
           (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
         2 ^ JWord.W32.to_uint j{hr})) = JWord.W32.to_uint((JWord.W32.of_int
        (JWord.W32.to_uint
           (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
             2 ^ JWord.W32.to_uint j{hr}))).
         smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp JWord.W16.of_uintK JWord.W16.to_uint_cmp JWord.W128.of_uintK JWord.W128.to_uint_cmp BArray1224.get32dE BArray1224.set32dE 
            BArray192.init_arrP BArray32.init_arrP BArray24.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_get SBArray1224_24.SBArray1224_24.is_init_cell_set BArray1224.init_arrP SBArray1224_24.SBArray1224_24.is_init_cell_set  SBArray1224_24.SBArray1224_24.Asmall.set32dE BArray32.set32dE JWord.W32.to_uint_eq StdOrder.IntOrder.ler_weexpn2l IntDiv.modz_small JWord.W32.to_uint_small JWord.W64.to_uint_small StdOrder.IntOrder.expr_gt0 StdOrder.IntOrder.Domain.exprS StdOrder.IntOrder.ler_wpmul2l StdOrder.IntOrder.Domain.exprD_nneg IntDiv.leq_div2r).

     move => aux9.
     have : !odd((JWord.W32.to_uint
                      (BArray68.get32d indices{hr}
                         (4 * JWord.W64.to_uint i{hr})) %/
                           2 ^ JWord.W32.to_uint j{hr})).
                           smt().
                   move => aux10.
                           have : (odd 16383).
                           smt(IntDiv.oddP).
                   move => aux11.



have := nodd_odd_tight_bound (JWord.W32.of_int
             (JWord.W32.to_uint
                (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
                  2 ^ JWord.W32.to_uint j{hr})) 16383.
            move => aux12.
            
have : (JWord.W32.to_uint
             (JWord.W32.of_int
                (JWord.W32.to_uint
                   (BArray68.get32d indices{hr}
                      (4 * JWord.W64.to_uint i{hr})) %/
                 2 ^ JWord.W32.to_uint j{hr})) <=
                        16383 - 1).
                        smt().
              move => aux13.

                        rewrite -aux9 in aux13.
              
       



  have : (JWord.W64.to_uint i{hr} * 2 ^ (14 - JWord.W32.to_uint j{hr}) +
JWord.W32.to_uint
  (
     (JWord.W32.of_int
        (JWord.W32.to_uint
           (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
         2 ^ JWord.W32.to_uint j{hr}))) + 1 <
17 * 2 ^ (14 - JWord.W32.to_uint j{hr}))
=>
  JWord.W64.to_uint i{hr} * 2 ^ (14 - JWord.W32.to_uint j{hr}) +
JWord.W32.to_uint
  (JWord.W32.(`^`)
     (JWord.W32.of_int
        (JWord.W32.to_uint
           (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
         2 ^ JWord.W32.to_uint j{hr})) JWord.W32.one) <
             17 * 2 ^ (14 - JWord.W32.to_uint j{hr}).
             smt().
             apply.
             rewrite JWord.W32.of_uintK.
             simplify.

have : (JWord.W32.to_uint
  (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
2 ^ JWord.W32.to_uint j{hr} %% 4294967296) = (JWord.W32.to_uint
  (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
    2 ^ JWord.W32.to_uint j{hr}).

    smt(JWord.W32.to_uint_cmp StdOrder.IntOrder.expr_gt0).
move => aux14.
    rewrite aux14.

have : odd(JWord.W32.to_uint
  (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
    2 ^ JWord.W32.to_uint j{hr} + 1).
    smt(IntDiv.oddP).
move => aux15.
    case : (JWord.W32.to_uint j{hr} = 0).
move => casse1.
    rewrite casse1.
    smt().
move => casse2.

    have : forall (x y : int), (!odd(x) /\ !odd(y)) => ((x < y) => ((x + 1) < y)).
    smt(IntDiv.oddWn).
move => aux16.

have : JWord.W64.to_uint i{hr} * 2 ^ (14 - JWord.W32.to_uint j{hr}) +
JWord.W32.to_uint
  (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
2 ^ JWord.W32.to_uint j{hr} < 17 * 2 ^ (14 - JWord.W32.to_uint j{hr}).


    have : (JWord.W64.to_uint i{hr} * 2 ^ (14 - JWord.W32.to_uint j{hr}) +
((16383) %/
2 ^ JWord.W32.to_uint j{hr}) < 17 * 2 ^ (14 - JWord.W32.to_uint j{hr})
)
=>
(JWord.W64.to_uint i{hr} * 2 ^ (14 - JWord.W32.to_uint j{hr}) +
JWord.W32.to_uint
  (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
    2 ^ JWord.W32.to_uint j{hr} < 17 * 2 ^ (14 - JWord.W32.to_uint j{hr})).

    smt(StdOrder.IntOrder.expr_gt0 IntDiv.leq_div2r).


    apply.
have := StdOrder.IntOrder.Domain.exprD_nneg 2 ((14 - JWord.W32.to_uint j{hr})) (JWord.W32.to_uint j{hr}).
move => aux17.
have : (0 <= 14 - JWord.W32.to_uint j{hr} =>
           0 <= JWord.W32.to_uint j{hr} =>
           2 ^ (14) =
  2 ^ (14 - JWord.W32.to_uint j{hr}) * 2 ^ JWord.W32.to_uint j{hr}).
  have : (14 - JWord.W32.to_uint j{hr} + JWord.W32.to_uint j{hr}) = 14.
  smt().
move => aux18.
  move : aux17.
rewrite aux18.
  smt().
move => aux18.
    have : (((2 ^ 14) - 1) %/ 2 ^ JWord.W32.to_uint j{hr}) = (((2 ^ 14) %/ 2 ^ JWord.W32.to_uint j{hr}) - 1).
  have : (2 ^ 14) = (2 ^ (14 - JWord.W32.to_uint j{hr})) * (2 ^ JWord.W32.to_uint j{hr}).
apply aux18.
  smt().
  smt(JWord.W32.to_uint_cmp).
move => aux19.

  rewrite aux18.
  smt().
  smt(JWord.W32.to_uint_cmp).
  have := (IntDiv.divzMDl (2 ^ (14 - JWord.W32.to_uint j{hr})) (-1) (2 ^ JWord.W32.to_uint j{hr})).
move => aux20.
  rewrite aux20.
  smt(StdOrder.IntOrder.expr_gt0).
  have := (IntDiv.divzMDl (2 ^ (14 - JWord.W32.to_uint j{hr})) 0 (2 ^ JWord.W32.to_uint j{hr})).
move => aux21.
  rewrite aux21.
  smt(StdOrder.IntOrder.expr_gt0).
  smt(StdOrder.IntOrder.expr_gt0).
move => aux19.

have : 16383 = (2 ^ 14) - 1.
  smt().
move => aux20.
  rewrite aux20.
rewrite aux19.

  have : (2 ^ 14 %/ 2 ^ JWord.W32.to_uint j{hr}) = (2 ^ (14 -JWord.W32.to_uint j{hr})).

have : 2 ^ 14 =
  2 ^ (14 - JWord.W32.to_uint j{hr}) * 2 ^ JWord.W32.to_uint j{hr}.
  apply aux18.
smt().
  smt(JWord.W32.to_uint_cmp).
move => aux21.
rewrite aux21.

      
  smt().
  smt().
move => aux17.
have : !odd(JWord.W64.to_uint i{hr} * 2 ^ (14 - JWord.W32.to_uint j{hr}) +
JWord.W32.to_uint
  (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
    2 ^ JWord.W32.to_uint j{hr}).

    have : !odd(JWord.W64.to_uint i{hr} * 2 ^ (14 - JWord.W32.to_uint j{hr})).

  have := (StdOrder.IntOrder.Domain.exprS 2 ((13 - JWord.W32.to_uint j{hr}))).
move => aux18.
  rewrite aux18.
  have mAx : JWord.W32.to_uint (JWord.W32.of_int 14) = 14 by rewrite JWord.W32.of_uintK.
smt(JWord.W32.ultE JWord.W32.to_uint_cmp).
  smt().
move => aux18.
  smt(IntDiv.oddWn).
move => aux19.

  have : !odd(17 * 2 ^ (14 - JWord.W32.to_uint j{hr})).
  have := (StdOrder.IntOrder.Domain.exprS 2 ((13 - JWord.W32.to_uint j{hr}))).
move => aux20.
    rewrite aux20.
clear aux aux2 aux2 aux4 aux5 aux6 aux7 aux8 aux9 aux10 aux11 aux12 aux13 aux14 aux15 aux16 aux17 aux19 aux20.
  smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
  smt().
smt().

  smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
  move : H6.
  rewrite /JWord.W32.(\ult).
  rewrite /JWord.W32.(\ule).
  rewrite /JWord.W32.(+).
  rewrite /JWord.W32.ulift2.
  smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).

                                                               rewrite /JWord.W32.(`>>`).
 have : ((JWord.W32.(`>>>`)
     (JWord.W32.(`^`)
        (JWord.W32.of_int
           (JWord.W32.to_uint
              (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
            2 ^ JWord.W32.to_uint j{hr})) JWord.W32.one)
     (JWord.W8.to_uint JWord.W8.one))) = ((JWord.W32.(`>>>`)
     (
        (JWord.W32.of_int
           (JWord.W32.to_uint
              (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
            2 ^ JWord.W32.to_uint j{hr})))
     (JWord.W8.to_uint JWord.W8.one))).
       smt().
 move => aux.
       rewrite aux.

       have : 
  ((JWord.W32.(`>>>`)
     (JWord.W32.of_int
        (JWord.W32.to_uint
           (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
         2 ^ JWord.W32.to_uint j{hr})) (JWord.W8.to_uint JWord.W8.one))
  =

  (JWord.W32.of_int
     (JWord.W32.to_uint
        (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
      2 ^ JWord.W32.to_uint (JWord.W32.(+) j{hr} JWord.W32.one)))
  )
 =>
 (JWord.W32.(`^`)
  (JWord.W32.(`>>>`)
     (JWord.W32.of_int
        (JWord.W32.to_uint
           (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
         2 ^ JWord.W32.to_uint j{hr})) (JWord.W8.to_uint JWord.W8.one))
  JWord.W32.one =
JWord.W32.(`^`)
  (JWord.W32.of_int
     (JWord.W32.to_uint
        (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
      2 ^ JWord.W32.to_uint (JWord.W32.(+) j{hr} JWord.W32.one)))
          JWord.W32.one).
          smt().
  move => aux2.
          apply aux2.
    rewrite JWord.W32.shrDP.
    smt().

    rewrite /JWord.W32.(+).
    rewrite /JWord.W32.ulift2.
    rewrite JWord.W32.of_uintK.
    rewrite JWord.W32.of_uintK.
    simplify.



    have := StdOrder.IntOrder.ler_weexpn2l 2 _ (JWord.W32.to_uint j{hr}) 14 _.
    trivial.

    smt( JWord.W32.of_uintK JWord.W32.to_uint_cmp).
    simplify.
  move => aux3.

  
  have : (JWord.W32.to_uint
     (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
   2 ^ JWord.W32.to_uint j{hr} %% 4294967296) = (JWord.W32.to_uint
     (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
       2 ^ JWord.W32.to_uint j{hr}).

       have hx118 := JWord.W32.to_uint_cmp (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})).
have hp118 : 0 < 2 ^ JWord.W32.to_uint j{hr} by apply StdOrder.IntOrder.expr_gt0.
have hd0 : 0 <= JWord.W32.to_uint (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/ 2 ^ JWord.W32.to_uint j{hr} by apply IntDiv.divz_ge0; smt().
have hd1 : JWord.W32.to_uint (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/ 2 ^ JWord.W32.to_uint j{hr} <= JWord.W32.to_uint (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})).
  have := IntDiv.leq_trunc_div (JWord.W32.to_uint (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr}))) (2 ^ JWord.W32.to_uint j{hr}) _ _; 1,2: smt().
  smt().
have m32x : JWord.W32.modulus = 4294967296 by smt().
rewrite IntDiv.modz_small; smt().
   move => aux4.
       rewrite aux4.

       have := StdOrder.IntOrder.ler_weexpn2l 2 _ (JWord.W32.to_uint j{hr} + 1) 15 _.
    trivial.

       smt( JWord.W32.of_uintK JWord.W32.to_uint_cmp).
   simplify.
   move => aux5.

   have : (JWord.W32.to_uint
     (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
   2 ^ ((JWord.W32.to_uint j{hr} + 1) %% 4294967296) = (JWord.W32.to_uint
     (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
       2 ^ ((JWord.W32.to_uint j{hr} + 1)))).

       smt(JWord.W64.to_uint_cmp JWord.W32.to_uint_cmp).
 
   move => temp.
       rewrite temp.

       case : (1 <= JWord.W32.to_uint j{hr}).
 move => case1.

 have := exp_div_split2 (JWord.W32.to_uint
   (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr}))) ((JWord.W32.to_uint j{hr} + 1)).
 move => aux6.
     rewrite aux6.
     smt().
     smt().
 move => case2.
     have : (JWord.W32.to_uint j{hr} = 0).
     smt(JWord.W32.to_uint_cmp).
 move => aux6.
     rewrite aux6.
     simplify.
     trivial.

     rewrite /JWord.W64.(+).
     rewrite /JWord.W64.ulift2.
     rewrite /JWord.W32.(+).
     rewrite /JWord.W32.ulift2.
     rewrite JWord.W64.of_uintK.
     rewrite JWord.W64.of_uintK.
     rewrite JWord.W32.of_uintK.
  rewrite JWord.W32.of_uintK.

     smt(JWord.W64.to_uint_cmp JWord.W32.to_uint_cmp).
   rewrite SBArray6120_24.SBArray6120_24.is_init_cell_set.
   case : (JWord.W64.to_uint offset{hr} <= i0).
 move => case1.
   have : ((true && i0 < 24 + JWord.W64.to_uint offset{hr}) /\ 0 <= i0 < 6120) = true.
   move : H25.
   rewrite /JWord.W64.(+).
   rewrite /JWord.W64.ulift2.
   smt(JWord.W64.of_uintK StdOrder.IntOrder.expr_gt0).
 move => aux.
   rewrite aux.
   smt().
 smt().

auto .
ecall (__fors_skgen_proof param_5 b_param_0 param_4 (BArray24.init_arr
                                                    (JWord.W8.of_int 255)) 
       param_3 (BArray24.init_arr (JWord.W8.of_int 255)) param_2 (BArray32.init_arr
                                                           (JWord.W8.of_int 255)) 
       param_1).
                                                             auto .
                                                             progress.
                                                             smt(JWord.W64.to_uint_cmp).
                                                             smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
                                                       
                                                             smt(JWord.W64.to_uint_cmp).
                                                             smt().
                                                             smt(BArray32.init_arrP BArray24.init_arrP).
                                                             smt(BArray32.init_arrP BArray24.init_arrP).
                                                             smt(BArray32.init_arrP BArray24.init_arrP).
                                                             smt(BArray32.init_arrP BArray24.init_arrP).
                                                             rewrite /JWord.W64.(+).
                                                             rewrite /JWord.W64.ulift2.
                                                             rewrite JWord.W64.of_uintK.
                                                             rewrite JWord.W64.of_uintK.
                                                             smt().

                                                             rewrite /BArray6120.is_init.
                                                       move => a b c.
                                                             rewrite (SBArray6120_24.SBArray6120_24.is_init_cell_set b_sig_fors{hr} (BArray24.init_arr (JWord.W8.of_int 255)) (JWord.W64.to_uint offset{hr}) a).
                                                             case : (JWord.W64.to_uint offset{hr} <= a).
                                                       move => case1.
                                                       have : ((true && a < 24 + JWord.W64.to_uint offset{hr}) /\ 0 <= a < 6120) = true.
                                                             smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
                                                       move => aux.
                                                             rewrite aux.
                                                             smt().

                                                             have : ((false && a < 24 + JWord.W64.to_uint offset{hr}) /\ 0 <= a < 6120) = false.
                                                             smt().
                                                       smt().
                                                             smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
                                                        smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
                                                             rewrite /JWord.W64.(+).
                                                             rewrite /JWord.W64.ulift2.
                                                             rewrite JWord.W64.of_uintK.
                                                             rewrite JWord.W64.of_uintK.
                                                             simplify.

                                                             have : JWord.W32.to_uint j0 = 14.
                                                             move : H24.
                                                       rewrite /JWord.W32.(\ult).
                                                             smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).

                                                             smt().


auto .
ecall (baseb_fors____base_b_proof param_0 b_param_1 param (BArray30.init_arr
                                                          (JWord.W8.of_int 255))).
                                                            auto .
                                                            progress.
smt(BArray30.init_arrP).
move : H11.
rewrite and_iota.
rewrite /JUtils.(`<<`).
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
have m22 : JWord.W64.to_uint (JWord.W64.of_int 17) = 17 by rewrite JWord.W64.of_uintK.
have hi0 : JWord.W64.to_uint i0 = 17 by smt(JWord.W64.uleE JWord.W64.ultE).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp StdOrder.IntOrder.Domain.exprS).
smt(BArray32.init_arrP BArray24.init_arrP).
qed.

lemma __fors_sign_proof _sig_fors _b_sig_fors _md _b_md _skseed _b_skseed _pkseed _b_pkseed _adrs _b_adrs :
      (__fors_sign_spec _sig_fors _b_sig_fors _md _b_md _skseed _b_skseed
      _pkseed _b_pkseed _adrs _b_adrs).
proof.
rewrite /__fors_sign_spec .
proc; auto .
ecall (fors_sign_proof param_3 b_param param_2 (BArray30.init_arr
                                               (JWord.W8.of_int 255)) param_1 
       (BArray24.init_arr (JWord.W8.of_int 255)) param_0 (BArray24.init_arr
                                                   (JWord.W8.of_int 255)) param 
       (BArray32.init_arr (JWord.W8.of_int 255))).
auto .
smt(BArray32.init_arrP BArray24.init_arrP BArray30.init_arrP BArray6120.init_arrP).
qed .

lemma fors_pkfromsig_proof _pk_fors _b_pk_fors _sig_fors _b_sig_fors _md _b_md _pkseed _b_pkseed _adrs _b_adrs :
      (fors_pkfromsig_spec _pk_fors _b_pk_fors _sig_fors _b_sig_fors 
      _md _b_md _pkseed _b_pkseed _adrs _b_adrs).
proof.
rewrite /fors_pkfromsig_spec .
proc; auto .
ecall (__T_k_proof param_45 b_param_0 param_44 (BArray24.init_arr
                                               (JWord.W8.of_int 255)) param_43 
       (BArray32.init_arr (JWord.W8.of_int 255)) param_42 b_param).
auto .
ecall (__adrs_set_key_pair_addr_proof param_41 (BArray32.init_arr
                                               (JWord.W8.of_int 255)) param_40).
auto .
ecall (__adrs_get_key_pair_addr_proof param_39 (BArray32.init_arr
                                               (JWord.W8.of_int 255))).
auto .
ecall (__adrs_set_type_and_clear_proof param_38 (BArray32.init_arr
                                                (JWord.W8.of_int 255)) param_37).
auto .
ecall (__adrs_clone_proof param_36 b_param_1 param_35 (BArray32.init_arr
                                                      (JWord.W8.of_int 255))).
                                                        auto .

                                                                                                                 have :  forall (n x : int), (2 <= x) => n %/ (2 ^ x) = ((n %/ 2) %/ (2 ^ (x - 1))).

                                                             move => n x hx.
have hexp : 2 ^ x = 2 * 2 ^ (x-1).
  smt( StdOrder.IntOrder.Domain.exprS).
have h2pos : 0 < 2^(x-1) by smt(StdOrder.IntOrder.expr_gt0).
                                                               smt(IntDiv.divz_mulp).
                                                             move => exp_div_split.

                                                                                                                        have :  forall (n x : int), (2 <= x) => n %/ (2 ^ x) = (((n %/ (2 ^ (x - 1))) %/ 2)).

                                                             move => n x hx.
have hexp : 2 ^ x = 2 * 2 ^ (x-1).
  smt( StdOrder.IntOrder.Domain.exprS).
have h2pos : 0 < 2^(x-1) by smt(StdOrder.IntOrder.expr_gt0).
                                                               smt(IntDiv.divz_mulp).
                                                             move => exp_div_split2.

while ((JWord.W64.(\ule) JWord.W64.zero i) /\
      (JWord.W64.(\ule) i (JWord.W64.of_int 17)) /\
      (JWord.W64.to_uint offset = (JWord.W64.to_uint i) * 15 * 24) /\
      (forall (k : int), ((0 <= k /\ k < 17) =>
      (JWord.W32.to_uint (BArray68.get32d indices (4 * k)) < 16384))) /\
      (BArray6120.is_init b_sig_fors 0 6120) /\
      (JWord.W64.to_uint offset_roots = (JWord.W64.to_uint i) * 24) /\
      (BArray408.is_init b_roots 0 (JWord.W64.to_uint offset_roots)) /\
      (BArray68.is_init b_indices 0 68)).
auto .
ecall (__copy_nbytes_proof param_34 b_param_2 param_33 (BArray24.init_arr
                                                       (JWord.W8.of_int 255))).
auto .
while ((JWord.W32.(\ule) JWord.W32.zero j) /\
      (JWord.W32.(\ule)) j (JWord.W32.of_int 14) /\
      (JWord.W64.(\ule) JWord.W64.zero i) /\
      (JWord.W64.(\ult) i (JWord.W64.of_int 17)) /\
      (forall (k : int), ((0 <= k /\ k < 17) =>
      (JWord.W32.to_uint (BArray68.get32d indices (4 * k)) < 16384))) /\
      (idx_auth = JWord.W32.of_int((JWord.W32.to_uint
      (BArray68.get32d indices (4 * JWord.W64.to_uint i)) %/ (2 ^ (JWord.W32.to_uint j))))  /\
      (JWord.W64.to_uint offset = (JWord.W64.to_uint i) * 15 * 24 + (JWord.W32.to_uint j + 1) * 24) /\
      (BArray6120.is_init b_sig_fors 0 111200))).
auto .
ecall (__copy_nbytes_proof param_32 (BArray24.init_arr (JWord.W8.of_int 255)) 
       param_31 (BArray24.init_arr (JWord.W8.of_int 255))).
auto .
ecall (__H_proof param_30 b_param_3 param_29 (BArray24.init_arr
                                             (JWord.W8.of_int 255)) param_28 
       (BArray32.init_arr (JWord.W8.of_int 255)) param_27 (BArray24.init_arr
                                                    (JWord.W8.of_int 255)) 
       param_26 (BArray24.init_arr (JWord.W8.of_int 255))).
                                                      auto .
                                                      sp.
                                                      seq 1 : (#pre /\ BArray32.is_init aux_2 0 32).

                                                      ecall (__adrs_set_tree_height_proof param_11 (BArray32.init_arr (JWord.W8.of_int 255)) param_10).
                                                auto.
                                                      smt(SBArray1224_24.SBArray1224_24.Asmall.init_arrP BArray32.init_arrP JWord.W64.to_uint_small).
                                                      sp.
                                                      if.
                                                      sp.
                                                      if.
                                                auto.
                                                
ecall (__copy_nbytes_proof param_18 b_param_5 param_17 b_param_4).
auto .
ecall (__copy_nbytes_proof param_16 b_param_6 param_15 (BArray24.init_arr
                                                       (JWord.W8.of_int 255))).
auto .
ecall (__adrs_set_tree_index_proof param_14 (BArray32.init_arr
                                            (JWord.W8.of_int 255)) param_13).
auto .
ecall (__adrs_get_tree_index_proof param_12 (BArray32.init_arr
                                            (JWord.W8.of_int 255))).
                                              auto .

progress; try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
                                              smt(BArray32.init_arrP BArray24.init_arrP).
                                              smt(JWord.W64.to_uint_cmp).
                                              smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
                                              rewrite /BArray32.is_init.
                                        move => a b c.
                                              rewrite (SBArray6120_24.SBArray6120_24.is_init_cell_get b_sig_fors{hr} a (JWord.W64.to_uint offset{hr})).
                                              trivial.
                                              smt().
                                              smt().
                                              smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
                                              move : H6.
                                              rewrite /JWord.W32.(\ult).
                                              rewrite /JWord.W32.(\ule).
                                              rewrite /JWord.W32.(+).
                                              rewrite /JWord.W32.ulift2.
                                              smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).

                                              rewrite /JWord.W32.(`>>`).
                                              rewrite JWord.W32.shrDP.
                                              smt().
                                              rewrite /JWord.W32.(+).
                                        rewrite /JWord.W32.ulift2.
                                              rewrite JWord.W32.of_uintK.
                                              rewrite JWord.W32.of_uintK.
                                              simplify.

                                              have := StdOrder.IntOrder.ler_weexpn2l 2 _ (JWord.W32.to_uint j{hr}) 14 _.
                                              trivial.
                                              smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).

                                        have : (JWord.W32.to_uint
     (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
   2 ^ JWord.W32.to_uint j{hr} %% 4294967296) = (JWord.W32.to_uint
     (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
       2 ^ JWord.W32.to_uint j{hr}).
       smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp StdOrder.IntOrder.expr_gt0).
   move => temp.
       rewrite temp.

       have := StdOrder.IntOrder.ler_weexpn2l 2 _ (JWord.W32.to_uint j{hr} + 1) 15 _.
       trivial.
       smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
   move => aux.

   have : (JWord.W32.to_uint
     (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
   2 ^ ((JWord.W32.to_uint j{hr} + 1) %% 4294967296) = (JWord.W32.to_uint
     (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
       2 ^ ((JWord.W32.to_uint j{hr} + 1)))).
       smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
 move => temp2.
       rewrite temp2.

       case : (1 <= (JWord.W32.to_uint j{hr})).
 move => case1.

 have := exp_div_split2 (JWord.W32.to_uint
   (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr}))) ((JWord.W32.to_uint j{hr} + 1)).
 move => aux2.
     rewrite aux2.
     smt().
 move => aux3.
     smt().
 move => case2.
     have : (JWord.W32.to_uint j{hr} = 0).
     smt(JWord.W32.to_uint_cmp).
 move => aux2.
     rewrite aux2.
     smt().

     rewrite /JWord.W64.(+).
     rewrite /JWord.W64.ulift2.
     rewrite /JWord.W32.(+).
     rewrite /JWord.W32.ulift2.
     rewrite JWord.W32.of_uintK.
     rewrite JWord.W32.of_uintK.
     rewrite JWord.W64.of_uintK.
     rewrite JWord.W64.of_uintK.
     smt(JWord.W64.to_uint_cmp JWord.W32.to_uint_cmp).

auto .

ecall (__copy_nbytes_proof param_25 b_param_7 param_24 (BArray24.init_arr
                                                       (JWord.W8.of_int 255))).
auto .
ecall (__copy_nbytes_proof param_23 b_param_9 param_22 b_param_8).
auto .
ecall (__adrs_set_tree_index_proof param_21 (BArray32.init_arr
                                            (JWord.W8.of_int 255)) param_20).
auto .
ecall (__adrs_get_tree_index_proof param_19 (BArray32.init_arr
                                            (JWord.W8.of_int 255))).
                                              auto .

progress; try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
                                              smt(BArray32.init_arrP BArray24.init_arrP).
                                              smt(JWord.W64.to_uint_cmp).
                                              smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp JWord.W32.of_uintK JWord.W32.to_uint_cmp).
                                              rewrite /BArray32.is_init.
                                        move => a b c.

                                              rewrite (SBArray6120_24.SBArray6120_24.is_init_cell_get b_sig_fors{hr} a (JWord.W64.to_uint offset{hr})).
                                              trivial.
                                              smt().
                                              smt().
                                              smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
                                              move : H6.
                                              rewrite /JWord.W32.(\ult).
                                              rewrite /JWord.W32.(\ule).
                                              rewrite /JWord.W32.(+).
                                              rewrite /JWord.W32.ulift2.
                                              smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).

                                         rewrite /JWord.W32.(`>>`).
                                              rewrite JWord.W32.shrDP.
                                              smt().
                                              rewrite /JWord.W32.(+).
                                        rewrite /JWord.W32.ulift2.
                                              rewrite JWord.W32.of_uintK.
                                              rewrite JWord.W32.of_uintK.
                                              simplify.

                                              have := StdOrder.IntOrder.ler_weexpn2l 2 _ (JWord.W32.to_uint j{hr}) 14 _.
                                              trivial.
                                              smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).

                                        have : (JWord.W32.to_uint
     (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
   2 ^ JWord.W32.to_uint j{hr} %% 4294967296) = (JWord.W32.to_uint
     (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
       2 ^ JWord.W32.to_uint j{hr}).
       smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp StdOrder.IntOrder.expr_gt0).
   move => temp.
       rewrite temp.

       have := StdOrder.IntOrder.ler_weexpn2l 2 _ (JWord.W32.to_uint j{hr} + 1) 15 _.
       trivial.
       smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
   move => aux.

   have : (JWord.W32.to_uint
     (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
   2 ^ ((JWord.W32.to_uint j{hr} + 1) %% 4294967296) = (JWord.W32.to_uint
     (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr})) %/
       2 ^ ((JWord.W32.to_uint j{hr} + 1)))).
       smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
 move => temp2.
       rewrite temp2.

       case : (1 <= (JWord.W32.to_uint j{hr})).
 move => case1.

 have := exp_div_split2 (JWord.W32.to_uint
   (BArray68.get32d indices{hr} (4 * JWord.W64.to_uint i{hr}))) ((JWord.W32.to_uint j{hr} + 1)).
 move => aux2.
     rewrite aux2.
     smt().
 move => aux3.
     smt().
 move => case2.
     have : (JWord.W32.to_uint j{hr} = 0).
     smt(JWord.W32.to_uint_cmp).
 move => aux2.
     rewrite aux2.
     smt().

     rewrite /JWord.W64.(+).
     rewrite /JWord.W64.ulift2.
     rewrite /JWord.W32.(+).
     rewrite /JWord.W32.ulift2.

     rewrite JWord.W64.of_uintK.
     rewrite JWord.W64.of_uintK.
     rewrite JWord.W32.of_uintK.
     rewrite JWord.W32.of_uintK.
 
     smt(JWord.W64.to_uint_cmp JWord.W32.to_uint_cmp).
     exfalso.
     smt().
 auto.

ecall (__F_proof param_9 (BArray24.init_arr (JWord.W8.of_int 255)) param_8 
       (BArray24.init_arr (JWord.W8.of_int 255)) param_7 (BArray32.init_arr
                                                   (JWord.W8.of_int 255))).
auto .
ecall (__adrs_set_tree_index_proof param_6 (BArray32.init_arr (JWord.W8.of_int 255)
                                           ) param_5).
auto .
ecall (__adrs_set_tree_height_proof param_4 (BArray32.init_arr
                                            (JWord.W8.of_int 255)) param_3).
auto .
ecall (__copy_nbytes_proof param_2 b_param_11 param_1 b_param_10).
                                              auto .

progress; try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
                                              smt(JWord.W64.to_uint_cmp).
                                              smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).

                                              rewrite /BArray32.is_init.
                                        move => a b c.
                                              rewrite (SBArray6120_24.SBArray6120_24.is_init_cell_get b_sig_fors{hr} a (JWord.W64.to_uint offset{hr})).
                                              trivial.
                                              smt().
                                              smt().
                                              smt(BArray32.init_arrP BArray24.init_arrP).
                                              smt().
                                              smt().
                                              smt().
                                              rewrite /JWord.W64.(+).
                                              rewrite /JWord.W64.ulift2.
                                              rewrite JWord.W64.of_uintK.
                                              rewrite JWord.W64.of_uintK.
                                              smt().
                                              smt().
                                              smt().
                                              smt().
                                              smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
                                              smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
                                              have : (JWord.W32.to_uint j0 = 14).
                                              move : H34 H36.
                                              rewrite /JWord.W32.(\ult).
                                              rewrite /JWord.W32.(\ule).
                                              smt().
                                              rewrite /JWord.W64.(+).
                                              rewrite /JWord.W64.ulift2.
                                              smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp).
                                              smt(JWord.W64.to_uint_cmp JWord.W32.to_uint_cmp JWord.W64.to_uint_small).
                                              rewrite /BArray408.is_init.
                                        move => a b c.
                                              rewrite (SBArray408_24.SBArray408_24.is_init_cell_set b_roots{hr} (BArray24.init_arr (JWord.W8.of_int 255)) (JWord.W64.to_uint offset_roots{hr}) a).
                                              case : (JWord.W64.to_uint offset_roots{hr} <= a).
                                        move => case1.
                                        have : ((true && a < 24 + JWord.W64.to_uint offset_roots{hr}) /\ 0 <= a < 408) = true.
                                        
                                        
                                              smt(JWord.W64.to_uint_cmp JWord.W64.to_uint_small).
                                        
                                        move => aux.
                                              rewrite aux.
                                              smt().
                                        smt().
                                        
                                        auto.

ecall (baseb_fors____base_b_proof param_0 b_param_12 param (BArray30.init_arr
                                                           (JWord.W8.of_int 255))).
                                                             auto .
                                                             progress; try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
smt(BArray30.init_arrP).
move : H11.
rewrite and_iota.
rewrite /JUtils.(`<<`).
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
smt(BArray32.init_arrP BArray24.init_arrP).
smt(BArray32.init_arrP BArray24.init_arrP).
have m22 : JWord.W64.to_uint (JWord.W64.of_int 17) = 17 by rewrite JWord.W64.of_uintK.
have hi0 : JWord.W64.to_uint i0 = 17 by smt(JWord.W64.uleE JWord.W64.ultE).
smt(JWord.W64.of_uintK JWord.W64.to_uint_cmp StdOrder.IntOrder.Domain.exprS).
qed.

lemma __fors_pkfromsig_proof _pk_fors _b_pk_fors _sig_fors _b_sig_fors _md _b_md _pkseed _b_pkseed _adrs _b_adrs :
      (__fors_pkfromsig_spec _pk_fors _b_pk_fors _sig_fors _b_sig_fors 
      _md _b_md _pkseed _b_pkseed _adrs _b_adrs).
proof.
rewrite /__fors_pkfromsig_spec .
proc; auto .
ecall (fors_pkfromsig_proof param_3 b_param param_2 (BArray6120.init_arr
                                                    (JWord.W8.of_int 255)) 
       param_1 (BArray30.init_arr (JWord.W8.of_int 255)) param_0 (BArray24.init_arr
                                                           (JWord.W8.of_int 255)) 
       param (BArray32.init_arr (JWord.W8.of_int 255))).
auto .
smt(BArray32.init_arrP BArray24.init_arrP BArray30.init_arrP BArray6120.init_arrP).
qed .

lemma __indices_to_regs_proof _tmp_idx_tree _b_tmp_idx_tree _tmp_idx_leaf _b_tmp_idx_leaf :
      (__indices_to_regs_spec _tmp_idx_tree _b_tmp_idx_tree _tmp_idx_leaf
      _b_tmp_idx_leaf).
proof.
rewrite /__indices_to_regs_spec .
proc; auto .
while (0 <= i /\ i <= 2).
auto .
smt().
auto .
while (0 <= i /\ i <= 7 /\ BArray12.is_init b_idx_tree 0 12).
auto .
smt(BArray12.is_init_cell_set32d).
auto .
progress.
smt(BArray12.is_init_cell_set32d).
smt(BArray12.is_init_cell_set32d).
smt(BArray12.is_init_cell_set32d).

have : (forall (w : JWord.W32.t), (JWord.W32.(\ult) (JWord.W32.(`&`) w (JWord.W32.of_int 511))
       (JWord.W32.of_int 512))).
rewrite /JWord.W32.(\ult).
rewrite JWord.W32.of_uintK.
have : 511 = (2 ^ 9) - 1.
smt().
move: JWord.W32.to_uint_and_mod.
move => hkeq h15eq w.
have temp := hkeq 9 w _.
smt().
smt().
move => less_than_15_after_mask.
rewrite /JUtils.(`<<`).
smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).
qed .

lemma slh_keygen_internal__proof _sk _b_sk _pk _b_pk _keyrnd _b_keyrnd :
      (slh_keygen_internal__spec _sk _b_sk _pk _b_pk _keyrnd _b_keyrnd).
proof.
rewrite /slh_keygen_internal__spec .
proc; auto .
ecall (__copy_nbytes_proof param_17 b_param_0 param_16 b_param).
auto .
ecall (__xmss_node_proof param_15 b_param_3 param_14 b_param_2 param_13 
       param_12 param_11 b_param_1 param_10 (BArray32.init_arr
                                            (JWord.W8.of_int 255))).
auto .
ecall (__adrs_set_layer_addr_proof param_9 (BArray32.init_arr (JWord.W8.of_int 255)
                                           ) param_8).
auto .
ecall (__adrs_init_proof param_7 b_param_4).
auto .
ecall (__copy_nbytes_proof param_6 b_param_6 param_5 b_param_5).
auto .
ecall (__copy_nbytes_proof param_4 b_param_8 param_3 b_param_7).
auto .
ecall (__copy_nbytes_proof param_2 b_param_10 param_1 b_param_9).
auto .
ecall (__copy_nbytes_proof param_0 b_param_12 param b_param_11).
                                               auto .
                                               progress.
                                               rewrite /BArray32.is_init.
                                         move => a b c.
                                           rewrite (SBArray72_24.SBArray72_24.is_init_cell_get b_keyrnd{hr} a 0).
                                           trivial.
                                           smt().
                                           smt().
                                           rewrite /BArray32.is_init.
                                         move => a b c.
                                           rewrite (SBArray72_24.SBArray72_24.is_init_cell_get b_keyrnd{hr} a 24).
                                           trivial.
                                           smt().
                                           smt().

                                                   rewrite /BArray32.is_init.
                                         move => a b c.
                                           rewrite (SBArray72_24.SBArray72_24.is_init_cell_get b_keyrnd{hr} a 48).
                                           trivial.
                                           smt().
                                           smt().
                                           smt(BArray32.init_arrP BArray24.init_arrP).
                                           rewrite /BArray32.is_init.
                                         move => a b c.
                rewrite (SBArray96_24.SBArray96_24.is_init_cell_get ((SBArray96_24.SBArray96_24.set_sub
        (SBArray96_24.SBArray96_24.set_sub
           (SBArray96_24.SBArray96_24.set_sub b_sk{hr} 0
              (BArray24.init_arr (JWord.W8.of_int 255))) 24
           (BArray24.init_arr (JWord.W8.of_int 255))) 48
         (BArray24.init_arr (JWord.W8.of_int 255))))  a 0).
           trivial.
           smt().
                   rewrite (SBArray96_24.SBArray96_24.is_init_cell_set ((SBArray96_24.SBArray96_24.set_sub
        (SBArray96_24.SBArray96_24.set_sub b_sk{hr} 0
           (BArray24.init_arr (JWord.W8.of_int 255))) 24
         (BArray24.init_arr (JWord.W8.of_int 255)))) (BArray24.init_arr (JWord.W8.of_int 255)) 48 (0 + a)).
           have : (48 <= 0 + a < 24 + 48 /\ 0 <= 0 + a < 96) = false.
           smt().
   move => temp.
           rewrite temp.
           simplify.

   rewrite (SBArray96_24.SBArray96_24.is_init_cell_set (SBArray96_24.SBArray96_24.set_sub b_sk{hr} 0
       (BArray24.init_arr (JWord.W8.of_int 255))) (BArray24.init_arr (JWord.W8.of_int 255)) 24 a).
         have : (24 <= a < 24 + 24 /\ 0 <= a < 96) = false.
         smt().
   move => temp2.
         rewrite temp2.
         simplify.

         rewrite (SBArray96_24.SBArray96_24.is_init_cell_set b_sk{hr} (BArray24.init_arr (JWord.W8.of_int 255)) 0 a).

         have : (0 <= a < 24 + 0 /\ 0 <= a < 96) = true.
         smt().
   move => temp3.
         rewrite temp3.
         simplify.
         smt(BArray32.init_arrP BArray24.init_arrP).

         rewrite /BArray32.is_init.
   move => a b c.

                   rewrite (SBArray96_24.SBArray96_24.is_init_cell_get ((SBArray96_24.SBArray96_24.set_sub
        (SBArray96_24.SBArray96_24.set_sub
           (SBArray96_24.SBArray96_24.set_sub b_sk{hr} 0
              (BArray24.init_arr (JWord.W8.of_int 255))) 24
           (BArray24.init_arr (JWord.W8.of_int 255))) 48
         (BArray24.init_arr (JWord.W8.of_int 255))))  a 48).
           trivial.
           smt().
                   rewrite (SBArray96_24.SBArray96_24.is_init_cell_set ((SBArray96_24.SBArray96_24.set_sub
        (SBArray96_24.SBArray96_24.set_sub b_sk{hr} 0
           (BArray24.init_arr (JWord.W8.of_int 255))) 24
         (BArray24.init_arr (JWord.W8.of_int 255)))) (BArray24.init_arr (JWord.W8.of_int 255)) 48 (48 + a)).
           have : (48 <= 48 + a < 24 + 48 /\ 0 <= 48 + a < 96) = true.
           smt().
   move => temp.
           rewrite temp.
           simplify.

           smt(BArray32.init_arrP BArray24.init_arrP).

           rewrite /BArray32.is_init.
   move => a b c.
           rewrite (SBArray24_24.SBArray24_24.is_init_cell_get (BArray24.init_arr (JWord.W8.of_int 255)) a 0).
           trivial.
           smt().
           smt(BArray32.init_arrP BArray24.init_arrP).


                                           rewrite /BArray96.is_init.
                                         move => a b c.
                rewrite (SBArray96_24.SBArray96_24.is_init_cell_set (SBArray96_24.SBArray96_24.set_sub
        (SBArray96_24.SBArray96_24.set_sub
           (SBArray96_24.SBArray96_24.set_sub b_sk{hr} 0
              (BArray24.init_arr (JWord.W8.of_int 255))) 24
           (BArray24.init_arr (JWord.W8.of_int 255))) 48
         (BArray24.init_arr (JWord.W8.of_int 255))) (BArray24.init_arr (JWord.W8.of_int 255)) 72 a).
           case : (72 <= a).
     move => case1.

          have : ((true && a < 24 + 72) /\ 0 <= a < 96) = true.
           smt().
     move => temp.
           rewrite temp.
           simplify.
           smt(BArray32.init_arrP BArray24.init_arrP).
     move => case2.
           have : ((false && a < 24 + 72) /\ 0 <= a < 96) = false.
           smt().
     move => temp.
           rewrite temp.
     simplify.

 rewrite (SBArray96_24.SBArray96_24.is_init_cell_set ((SBArray96_24.SBArray96_24.set_sub
        (SBArray96_24.SBArray96_24.set_sub b_sk{hr} 0
           (BArray24.init_arr (JWord.W8.of_int 255))) 24
         (BArray24.init_arr (JWord.W8.of_int 255)))) (BArray24.init_arr (JWord.W8.of_int 255)) 48 a).
           case : (48 <= a).
   move => case0_1.
         have : ((true && a < 24 + 48) /\ 0 <= a < 96) = true.
         smt().
   move => temp2.
         rewrite temp2.
           simplify.
           smt(BArray32.init_arrP BArray24.init_arrP).
   move => case0_2.

           have : ((false && a < 24 + 48) /\ 0 <= a < 96) = false.
           smt().
   move => temp2.
           rewrite temp2.
           simplify.

   

         rewrite (SBArray96_24.SBArray96_24.is_init_cell_set ((SBArray96_24.SBArray96_24.set_sub b_sk{hr} 0
         (BArray24.init_arr (JWord.W8.of_int 255)))) (BArray24.init_arr (JWord.W8.of_int 255)) 24 a).
           case : (24 <= a).
   move => case1_1.

         have : ((true && a < 24 + 24) /\ 0 <= a < 96) = true.
         smt().
   move => temp3.
         rewrite temp3.
         simplify.
           smt(BArray32.init_arrP BArray24.init_arrP).
   move => case1_2.

           have : ((false && a < 24 + 24) /\ 0 <= a < 96) = false.
           smt().
   move => temp3.
           rewrite temp3.
           simplify.

           rewrite (SBArray96_24.SBArray96_24.is_init_cell_set b_sk{hr} (BArray24.init_arr (JWord.W8.of_int 255)) 0 a).
           have : (0 <= a < 24 + 0 /\ 0 <= a < 96) = true.
           smt().
   move => temp4.
           rewrite temp4.
           simplify.
   smt(BArray32.init_arrP BArray24.init_arrP).

           rewrite /BArray48.is_init.
   move => a b c.
   rewrite (SBArray48_24.SBArray48_24.is_init_cell_set ((SBArray48_24.SBArray48_24.set_sub b_pk{hr} 0
         (BArray24.init_arr (JWord.W8.of_int 255)))) ((BArray24.init_arr (JWord.W8.of_int 255))) 24 a).

           case : (24 <= a).
   move => case1.

          have : ((true && a < 24 + 24) /\ 0 <= a < 48) = true.
           smt().
   move => temp.
           rewrite temp.
           simplify.
           smt(BArray32.init_arrP BArray24.init_arrP).

   move => case2.
           have : ((false && a < 24 + 24) /\ 0 <= a < 48) = false.
           smt().
   move => temp.
           rewrite temp.
           simplify.

           rewrite (SBArray48_24.SBArray48_24.is_init_cell_set b_pk{hr} (BArray24.init_arr (JWord.W8.of_int 255)) 0 a).

           have : (0 <= a < 24 + 0 /\ 0 <= a < 48) = true.
           smt().
   move => temp1.
           rewrite temp1.
           simplify.
   smt(BArray32.init_arrP BArray24.init_arrP).
qed .

lemma __slh_keygen_internal_proof _sk _b_sk _pk _b_pk _keyrnd _b_keyrnd :
      (__slh_keygen_internal_spec _sk _b_sk _pk _b_pk _keyrnd _b_keyrnd).
proof.
rewrite /__slh_keygen_internal_spec .
proc; auto .
ecall (slh_keygen_internal__proof param_1 b_param_0 param_0 b_param param 
       (BArray72.init_arr (JWord.W8.of_int 255))).
auto .
smt(BArray48.init_arrP BArray72.init_arrP BArray96.init_arrP).
qed .

lemma slh_keygen_internal_avx2_proof _sk _b_sk _pk _b_pk _keyrnd _b_keyrnd :
      (slh_keygen_internal_avx2_spec _sk _b_sk _pk _b_pk _keyrnd _b_keyrnd).
proof.
rewrite /__slh_keygen_internal_spec .
proc; auto .
ecall (slh_keygen_internal__proof param_1 b_param_0 param_0 b_param param 
       (BArray72.init_arr (JWord.W8.of_int 255))).
auto .
smt(BArray48.init_arrP BArray72.init_arrP BArray96.init_arrP).
qed .

lemma slh_sign_internal__proof _sig_slh _b_sig_slh _ctx_msg_ptrs _b_ctx_msg_ptrs _ctx_msg_lens _b_ctx_msg_lens _sk _b_sk _addrnd _b_addrnd :
      (slh_sign_internal__spec _sig_slh _b_sig_slh _ctx_msg_ptrs
      _b_ctx_msg_ptrs _ctx_msg_lens _b_ctx_msg_lens _sk _b_sk _addrnd
      _b_addrnd).
proof.
rewrite /slh_sign_internal__spec .
proc; auto .
ecall (__ht_sign_proof param_38 b_param_1 param_37 (BArray24.init_arr
                                                   (JWord.W8.of_int 255)) param_36 
       b_param_0 param_35 b_param param_34 (BArray12.init_arr (JWord.W8.of_int 255)
                                           ) param_33).
auto .
ecall (__fors_pkfromsig_proof param_32 b_param_4 param_31 (
                                                          BArray6120.init_arr
                                                          (JWord.W8.of_int 255)) 
       param_30 b_param_3 param_29 b_param_2 param_28 (BArray32.init_arr
                                                      (JWord.W8.of_int 255))).
auto .
ecall (__fors_sign_proof param_27 b_param_8 param_26 b_param_7 param_25 
       b_param_6 param_24 b_param_5 param_23 (BArray32.init_arr
                                             (JWord.W8.of_int 255))).
auto .
ecall (__adrs_set_key_pair_addr_proof param_22 (BArray32.init_arr
                                               (JWord.W8.of_int 255)) param_21).
auto .
ecall (__adrs_set_type_and_clear_proof param_20 (BArray32.init_arr
                                                (JWord.W8.of_int 255)) param_19).
auto .
ecall (__adrs_set_tree_addr_proof param_18 (BArray32.init_arr (JWord.W8.of_int 255)
                                           ) param_17 (BArray12.init_arr
                                                      (JWord.W8.of_int 255))).
auto .
ecall (__indices_to_regs_proof param_16 b_param_10 param_15 b_param_9).
auto .
ecall (__H_msg_proof param_14 b_param_13 param_13 (BArray24.init_arr
                                                  (JWord.W8.of_int 255)) param_12 
       b_param_12 param_11 b_param_11 param_10 param_9 param_8 param_7).
auto .
ecall (__PRF_msg_proof param_6 b_param_15 param_5 b_param_14 param_4 
       (BArray24.init_arr (JWord.W8.of_int 255)) param_3 param_2 param_1 param_0).
auto .
ecall (__adrs_init_proof param b_param_16).
         auto .
         progress.
         rewrite /BArray24.is_init.
     move => a b c.
         rewrite (SBArray96_24.SBArray96_24.is_init_cell_get b_sk{hr} a 24).
         trivial.
         smt().
         smt(BArray32.init_arrP BArray24.init_arrP).
         smt(BArray32.init_arrP BArray24.init_arrP).

              rewrite /BArray24.is_init.
     move => a b c.
         rewrite (SBArray96_24.SBArray96_24.is_init_cell_get b_sk{hr} a 48).
         trivial.
         smt().
         smt().

                   rewrite /BArray24.is_init.
     move => a b c.
         rewrite (SBArray96_24.SBArray96_24.is_init_cell_get b_sk{hr} a 72).
         trivial.
         smt().
         smt().

         rewrite /BArray7.is_init.
     move => a b c.
         rewrite (SBArray39_7.SBArray39_7.is_init_cell_get (BArray39.init_arr (JWord.W8.of_int 255)) a 30).
         trivial.
         smt().
         smt(BArray39.init_arrP).

         move=> k hk1 hk2.
rewrite SBArray39_2.SBArray39_2.is_init_cell_get 1,2:/#.
apply (BArray39.init_arrP witness).

         move : H55.
         rewrite /JUtils.(`<<`).
         smt().

         smt(BArray12.init_arrP).

         try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
rewrite /BArray30.is_init.
     move => a b c.
         rewrite (SBArray39_30.SBArray39_30.is_init_cell_get (BArray39.init_arr (JWord.W8.of_int 255)) a 0).

         trivial.
         smt().
         smt(BArray39.init_arrP).

         rewrite /BArray24.is_init.
     move => a b c.

         rewrite (SBArray96_24.SBArray96_24.is_init_cell_get b_sk{hr} a 0).
         trivial.
         smt().
         smt().

         smt(BArray6120.init_arrP).
         smt(JWord.W32.of_uintK JWord.W32.to_uint_cmp).

         rewrite /BArray16224.is_init.
     move => a b c.
     rewrite (SBArray16224_10080.SBArray16224_10080.is_init_cell_set (SBArray16224_6120.SBArray16224_6120.set_sub
        (SBArray16224_24.SBArray16224_24.set_sub b_sig_slh{hr} 0
           (BArray24.init_arr (JWord.W8.of_int 255))) 24
         (BArray6120.init_arr (JWord.W8.of_int 255))) (BArray10080.init_arr (JWord.W8.of_int 255)) 6144 a).

           case : (6144 <= a).
     move => case1.

           have : ((true && a < 10080 + 6144) /\ 0 <= a < 16224) = true.
           smt().
     move => temp.
           rewrite temp.
           simplify.
           smt(BArray10080.init_arrP).

           simplify.

     rewrite (SBArray16224_6120.SBArray16224_6120.is_init_cell_set (SBArray16224_24.SBArray16224_24.set_sub b_sig_slh{hr} 0
         (BArray24.init_arr (JWord.W8.of_int 255))) (BArray6120.init_arr (JWord.W8.of_int 255)) 24 a).
     move => case2.
           case : (24 <= a).
     move => case0_1.
           have : ((true && a < 6120 + 24) /\ 0 <= a < 16224) = true.
           smt().
     move => temp.
           rewrite temp.
           simplify.
           smt(BArray6120.init_arrP).
           simplify.
     move => case0_2.

           rewrite (SBArray16224_24.SBArray16224_24.is_init_cell_set b_sig_slh{hr} (BArray24.init_arr (JWord.W8.of_int 255)) 0 a).

           have : (0 <= a < 24 + 0 /\ 0 <= a < 16224) = true.
           smt().

     move => temp.
           rewrite temp.
           simplify.
           smt().
qed.
     
lemma __slh_sign_internal_proof _sig_slh _b_sig_slh _ctx_msg_ptrs _b_ctx_msg_ptrs _ctx_msg_lens _b_ctx_msg_lens _sk _b_sk _addrnd _b_addrnd :
      (__slh_sign_internal_spec _sig_slh _b_sig_slh _ctx_msg_ptrs
      _b_ctx_msg_ptrs _ctx_msg_lens _b_ctx_msg_lens _sk _b_sk _addrnd
      _b_addrnd).
proof.
rewrite /__slh_sign_internal_spec .
proc; auto .
ecall (slh_sign_internal__proof param_3 b_param param_2 (BArray16.init_arr
                                                        (JWord.W8.of_int 255)) 
       param_1 (BArray16.init_arr (JWord.W8.of_int 255)) param_0 (
                                                           BArray96.init_arr
                                                           (JWord.W8.of_int 255)) 
       param (BArray24.init_arr (JWord.W8.of_int 255))).
auto .
smt(BArray16.init_arrP BArray32.init_arrP BArray24.init_arrP BArray96.init_arrP BArray16224.init_arrP).
qed .

lemma slh_sign_internal_avx2_proof _sig_slh _b_sig_slh _ctx_msg_ptrs _b_ctx_msg_ptrs _ctx_msg_lens _b_ctx_msg_lens _sk _b_sk _addrnd _b_addrnd :
      (slh_sign_internal_avx2_spec _sig_slh _b_sig_slh _ctx_msg_ptrs
      _b_ctx_msg_ptrs _ctx_msg_lens _b_ctx_msg_lens _sk _b_sk _addrnd
      _b_addrnd).
proof.
rewrite /__slh_sign_internal_spec .
proc; auto .
ecall (slh_sign_internal__proof param_3 b_param param_2 (BArray16.init_arr
                                                        (JWord.W8.of_int 255)) 
       param_1 (BArray16.init_arr (JWord.W8.of_int 255)) param_0 (
                                                           BArray96.init_arr
                                                           (JWord.W8.of_int 255)) 
       param (BArray24.init_arr (JWord.W8.of_int 255))).
auto .
smt(BArray16.init_arrP BArray32.init_arrP BArray24.init_arrP BArray96.init_arrP BArray16224.init_arrP).
qed .

lemma slh_verify_internal__proof _ctx_msg_ptrs _b_ctx_msg_ptrs _ctx_msg_lens _b_ctx_msg_lens _sig_slh _b_sig_slh _pk _b_pk :
      (slh_verify_internal__spec _ctx_msg_ptrs _b_ctx_msg_ptrs _ctx_msg_lens
      _b_ctx_msg_lens _sig_slh _b_sig_slh _pk _b_pk).
proof.
rewrite /slh_verify_internal__spec .
proc; auto .
ecall (__ht_verify_proof param_26 (BArray24.init_arr (JWord.W8.of_int 255)) 
       param_25 b_param_1 param_24 b_param_0 param_23 (BArray12.init_arr
                                                      (JWord.W8.of_int 255)) 
       param_22 param_21 b_param).
auto .
ecall (__fors_pkfromsig_proof param_20 b_param_5 param_19 b_param_4 param_18 
       b_param_3 param_17 b_param_2 param_16 (BArray32.init_arr
                                             (JWord.W8.of_int 255))).
auto .
ecall (__adrs_set_key_pair_addr_proof param_15 (BArray32.init_arr
                                               (JWord.W8.of_int 255)) param_14).
auto .
ecall (__adrs_set_type_and_clear_proof param_13 (BArray32.init_arr
                                                (JWord.W8.of_int 255)) param_12).
auto .
ecall (__adrs_set_tree_addr_proof param_11 (BArray32.init_arr (JWord.W8.of_int 255)
                                           ) param_10 (BArray12.init_arr
                                                      (JWord.W8.of_int 255))).
auto .
ecall (__indices_to_regs_proof param_9 b_param_7 param_8 b_param_6).
auto .
ecall (__H_msg_proof param_7 b_param_11 param_6 b_param_10 param_5 b_param_9 
       param_4 b_param_8 param_3 param_2 param_1 param_0).
auto .
ecall (__adrs_init_proof param b_param_12).
                                                        auto .
                                                        progress.
                                                        rewrite /BArray24.is_init.
                                                  move => a b c.
                                                        rewrite (SBArray16224_24.SBArray16224_24.is_init_cell_get b_sig_slh{hr} a 0).
                                                        trivial.
                                                        smt().
                                                        smt().

                                                                                                          rewrite /BArray24.is_init.
                                                  move => a b c.
                                                        rewrite (SBArray48_24.SBArray48_24.is_init_cell_get b_pk{hr} a 0).
                                                        trivial.
                                                        smt().
                                                        smt().

                                                      rewrite /BArray24.is_init.
                                                  move => a b c.
                                                        rewrite (SBArray48_24.SBArray48_24.is_init_cell_get b_pk{hr} a 24).
                                                        trivial.
                                                        smt().
                                                        smt().
                                                  
                                                        rewrite /is_init /valid /= .
                                                  move => a b c.

                                                        rewrite (SBArray39_7.SBArray39_7.is_init_cell_get (BArray39.init_arr (JWord.W8.of_int 255)) a 30).
                                                  trivial.
                                                        smt().
                                                        smt(BArray39.init_arrP).

                                                        move=> k hk1 hk2.
rewrite SBArray39_2.SBArray39_2.is_init_cell_get 1,2:/#.
apply (BArray39.init_arrP witness).
                                                        move : H43.
                                                        rewrite /JUtils.(`<<`).
                                                        smt().
                                                        smt(BArray12.init_arrP).
                                                        smt(BArray32.init_arrP BArray24.init_arrP).
                                                        rewrite /BArray6120.is_init.
                                                  move => a b c.
                                                        rewrite (SBArray16224_6120.SBArray16224_6120.is_init_cell_get b_sig_slh{hr} a 24).
                                                        trivial.
                                                        smt().
                                                        smt().
                                                        rewrite /BArray30.is_init.
                                                  move => a b c.
                                                        rewrite (SBArray39_30.SBArray39_30.is_init_cell_get (BArray39.init_arr (JWord.W8.of_int 255)) a 0).
                                                        trivial.
                                                        smt().
                                                        smt(BArray39.init_arrP).

                                                        try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray24.init_arrP witness)).
          try (move=> ? ? ?; apply (BArray32.init_arrP witness)).
          rewrite /BArray10080.is_init.
                                                  move => a b c.
                                                        rewrite (SBArray16224_10080.SBArray16224_10080.is_init_cell_get b_sig_slh{hr} a 6144).
                                                        trivial.
                                                        smt().
                                                  smt().
qed .

lemma __slh_verify_internal_proof _ctx_msg_ptrs _b_ctx_msg_ptrs _ctx_msg_lens _b_ctx_msg_lens _sig_slh _b_sig_slh _pk _b_pk :
      (__slh_verify_internal_spec _ctx_msg_ptrs _b_ctx_msg_ptrs _ctx_msg_lens
      _b_ctx_msg_lens _sig_slh _b_sig_slh _pk _b_pk).
proof.
rewrite /__slh_verify_internal_spec .
proc; auto .
ecall (slh_verify_internal__proof param_2 (BArray16.init_arr (JWord.W8.of_int 255)) 
       param_1 (BArray16.init_arr (JWord.W8.of_int 255)) param_0 (
                                                           BArray16224.init_arr
                                                           (JWord.W8.of_int 255)) 
       param (BArray48.init_arr (JWord.W8.of_int 255))).
auto .
smt(BArray16.init_arrP BArray48.init_arrP BArray16224.init_arrP).
qed .

lemma slh_verify_internal_avx2_proof _ctx_msg_ptrs _b_ctx_msg_ptrs _ctx_msg_lens _b_ctx_msg_lens _sig_slh _b_sig_slh _pk _b_pk :
      (slh_verify_internal_avx2_spec _ctx_msg_ptrs _b_ctx_msg_ptrs
      _ctx_msg_lens _b_ctx_msg_lens _sig_slh _b_sig_slh _pk _b_pk).
proof.
rewrite /__slh_verify_internal_spec .
proc; auto .
ecall (slh_verify_internal__proof param_2 (BArray16.init_arr (JWord.W8.of_int 255)) 
       param_1 (BArray16.init_arr (JWord.W8.of_int 255)) param_0 (
                                                           BArray16224.init_arr
                                                           (JWord.W8.of_int 255)) 
       param (BArray48.init_arr (JWord.W8.of_int 255))).
auto .
smt(BArray16.init_arrP BArray48.init_arrP BArray16224.init_arrP).
qed .

lemma slh_keygen_avx2_proof _sk _b_sk _pk _b_pk :
      (slh_keygen_avx2_spec _sk _b_sk _pk _b_pk).
proof.
rewrite /slh_keygen_avx2_spec .
proc; auto .
ecall (__slh_keygen_internal_proof param_1 b_param_0 param_0 b_param 
       param (BArray72.init_arr (JWord.W8.of_int 255))).
auto .
inline.
wp.
rnd.
auto.
smt(BArray48.init_arrP BArray72.init_arrP BArray96.init_arrP).
qed .

lemma slh_sign_avx2_proof _sig_slh _b_sig_slh _ctx_msg_ptrs _b_ctx_msg_ptrs _ctx_msg_lens _b_ctx_msg_lens _sk _b_sk _deterministic :
      (slh_sign_avx2_spec _sig_slh _b_sig_slh _ctx_msg_ptrs _b_ctx_msg_ptrs
      _ctx_msg_lens _b_ctx_msg_lens _sk _b_sk _deterministic).
proof.
rewrite /slh_sign_avx2_spec .
  proc; auto .
sp.
  if .
  sp.
  if.
  sp.
  seq 1 : ((  exists (param0 b_param_0_0 param_0_0 b_param_1_0 : BArray24.t),
    b_param_1 = b_addrnd /\
    param_0 = addrnd /\
    b_param_0 = SBArray96_24.SBArray96_24.get_sub b_sk 48 /\
    param = SBArray96_24.SBArray96_24.get_sub sk 48 /\
    (exists (b_addrnd0 : BArray24.t),
       b_addrnd = BArray24.init_arr JWord.W8.zero /\
       (addrnd = witness<:BArray24.t> /\
        b_addrnd0 = witness<:BArray24.t> /\
        b_param = witness<:BArray16224.t> /\
        b_param_0_0 = witness<:BArray24.t> /\
        b_param_1_0 = witness<:BArray24.t> /\
        b_result = witness<:BArray16224.t> /\
        (*b_result_0 = witness<:BArray24.t> /\*)
        param0 = witness<:BArray24.t> /\
        param_0_0 = witness<:BArray24.t> /\
        param_1 = witness<:BArray24.t> /\
        param_2 = witness<:BArray96.t> /\
        param_3 = witness<:BArray16.t> /\
        param_4 = witness<:BArray16.t> /\
        param_5 = witness<:BArray16224.t> /\
        (*result = witness<:BArray24.t> /\*)
        result_1 = witness<:BArray16224.t> /\
        (_deterministic = deterministic /\
         _b_sk = b_sk /\
         _sk = sk /\
         _b_ctx_msg_lens = b_ctx_msg_lens /\
         _ctx_msg_lens = ctx_msg_lens /\
         _b_ctx_msg_ptrs = b_ctx_msg_ptrs /\
         _ctx_msg_ptrs = ctx_msg_ptrs /\
         _b_sig_slh = b_sig_slh /\ _sig_slh = sig_slh) /\
        BArray16.is_init _b_ctx_msg_ptrs 0 8 /\
        BArray16.is_init _b_ctx_msg_lens 0 8 /\
        BArray16.is_init _b_ctx_msg_ptrs 8 8 /\
        BArray16.is_init _b_ctx_msg_lens 8 8 /\
        (((BArray16.is_init _b_ctx_msg_ptrs 0 16 /\
           BArray16.is_init _b_ctx_msg_lens 0 16) /\
          BArray96.is_init _b_sk 0 96) /\
         JMemory.is_valid 18446744073709551616 JMemory.Glob.mem_v
           (JWord.W64.to_uint (BArray16.get64d _ctx_msg_ptrs 0))
           (JWord.W64.to_uint (BArray16.get64d _ctx_msg_lens 0))) /\
        JMemory.is_valid 18446744073709551616 JMemory.Glob.mem_v
          (JWord.W64.to_uint (BArray16.get64d _ctx_msg_ptrs 8))
          (JWord.W64.to_uint (BArray16.get64d _ctx_msg_lens 8))) /\
       (BArray16.is_init b_ctx_msg_ptrs 0 16 /\
        BArray16.is_init b_ctx_msg_lens 0 16) /\
       BArray96.is_init b_sk 0 96) /\
    deterministic = JWord.W8.zero) /\ (BArray24.is_init b_result_0 0 24)).
  ecall (__copy_nbytes_proof param_0 b_param_1 param b_param_0).
  auto.
  progress.
  rewrite /BArray24.is_init.
move => a b c.
rewrite (SBArray96_24.SBArray96_24.is_init_cell_get b_sk{hr} a 48).
  trivial.
  smt().
         smt().
         smt().
         if.
         sp.
         if.
 auto.
ecall (__slh_sign_internal_proof param_5 b_param param_4 (BArray16.init_arr
                                                         (JWord.W8.of_int 255)) 
       param_3 (BArray16.init_arr (JWord.W8.of_int 255)) param_2 (
                                                           BArray96.init_arr
                                                           (JWord.W8.of_int 255)) 
       param_1 (BArray24.init_arr (JWord.W8.of_int 255))).
                                                             auto .
                                                             progress.
                                                             smt(BArray16.init_arrP).
                                                             smt(BArray16.init_arrP).
                                                             smt(BArray16.init_arrP).
                                                             smt(BArray16.init_arrP).
                                                             smt(BArray16.init_arrP).
                                                             smt(BArray16.init_arrP).
                                                             smt(BArray96.init_arrP).
                                                             smt(BArray32.init_arrP BArray24.init_arrP).
                                                             smt(BArray16224.init_arrP).
                                                             auto.
                                                             exfalso.
                                                       move => &hr.
                                                       move => *.
                                                             have : (b_param_0{hr} = SBArray96_24.SBArray96_24.get_sub b_sk{hr} 48).
                                                             smt().
                                                       move => aux.

                                       have : (BArray24.is_init b_param_0{hr} 0 24).
                                                             rewrite aux.
                                                             rewrite /BArray24.is_init.
                                                       move => a b c.
                                                             rewrite (SBArray96_24.SBArray96_24.is_init_cell_get b_sk{hr} a 48).
                                                             trivial.
                                                             smt().
                                                             smt().
                                                             smt().
                                                       seq 1 : (exists (b_addrnd0 : BArray24.t),
     b_addrnd = BArray24.init_arr JWord.W8.zero /\
     ((*addrnd = witness<:BArray24.t> /\
      b_addrnd0 = witness<:BArray24.t> /\*)
      b_param = witness<:BArray16224.t> /\
      b_param_0 = witness<:BArray24.t> /\
      b_param_1 = witness<:BArray24.t> /\
      b_result = witness<:BArray16224.t> /\
      b_result_0 = witness<:BArray24.t> /\
      param = witness<:BArray24.t> /\
      param_0 = witness<:BArray24.t> /\
      param_1 = witness<:BArray24.t> /\
      param_2 = witness<:BArray96.t> /\
      param_3 = witness<:BArray16.t> /\
      param_4 = witness<:BArray16.t> /\
      param_5 = witness<:BArray16224.t> /\
      result = witness<:BArray24.t> /\
      result_1 = witness<:BArray16224.t> /\
      (_deterministic = deterministic /\
       _b_sk = b_sk /\
       _sk = sk /\
       _b_ctx_msg_lens = b_ctx_msg_lens /\
       _ctx_msg_lens = ctx_msg_lens /\
       _b_ctx_msg_ptrs = b_ctx_msg_ptrs /\
       _ctx_msg_ptrs = ctx_msg_ptrs /\
       _b_sig_slh = b_sig_slh /\ _sig_slh = sig_slh) /\
      BArray16.is_init _b_ctx_msg_ptrs 0 8 /\
      BArray16.is_init _b_ctx_msg_lens 0 8 /\
      BArray16.is_init _b_ctx_msg_ptrs 8 8 /\
      BArray16.is_init _b_ctx_msg_lens 8 8 /\
      (((BArray16.is_init _b_ctx_msg_ptrs 0 16 /\
         BArray16.is_init _b_ctx_msg_lens 0 16) /\
        BArray96.is_init _b_sk 0 96) /\
       JMemory.is_valid 18446744073709551616 JMemory.Glob.mem_v
         (JWord.W64.to_uint (BArray16.get64d _ctx_msg_ptrs 0))
         (JWord.W64.to_uint (BArray16.get64d _ctx_msg_lens 0))) /\
      JMemory.is_valid 18446744073709551616 JMemory.Glob.mem_v
        (JWord.W64.to_uint (BArray16.get64d _ctx_msg_ptrs 8))
        (JWord.W64.to_uint (BArray16.get64d _ctx_msg_lens 8))) /\
     (BArray16.is_init b_ctx_msg_ptrs 0 16 /\
      BArray16.is_init b_ctx_msg_lens 0 16) /\
     BArray96.is_init b_sk 0 96 /\
  (deterministic <> JWord.W8.zero)).

    inline.
wp.
rnd.
    auto .

    if.
auto.
ecall (__slh_sign_internal_proof param_5 b_param param_4 (BArray16.init_arr
                                                         (JWord.W8.of_int 255)) 
       param_3 (BArray16.init_arr (JWord.W8.of_int 255)) param_2 (
                                                           BArray96.init_arr
                                                           (JWord.W8.of_int 255)) 
       param_1 (BArray24.init_arr (JWord.W8.of_int 255))).
                                                             auto .
                                                             progress.
                                                             smt(BArray16.init_arrP).
                                                             smt(BArray16.init_arrP).
                                                             smt(BArray16.init_arrP).
                                                             smt(BArray16.init_arrP).
                                                             smt(BArray16.init_arrP).
                                                             smt(BArray16.init_arrP).
                                                             smt(BArray96.init_arrP).
                                                             smt(BArray32.init_arrP BArray24.init_arrP).
                                                             smt(BArray16224.init_arrP).
                                                             auto.
                                                             exfalso.
                                                             smt().
qed .

lemma slh_verify_avx2_proof _ctx_msg_ptrs _b_ctx_msg_ptrs _ctx_msg_lens _b_ctx_msg_lens _sig _b_sig _pk _b_pk :
      (slh_verify_avx2_spec _ctx_msg_ptrs _b_ctx_msg_ptrs _ctx_msg_lens
      _b_ctx_msg_lens _sig _b_sig _pk _b_pk).
proof.
rewrite /slh_verify_avx2_spec .
  proc; auto .
sp.
  if .
if.
auto .
ecall (__slh_verify_internal_proof param_2 (BArray16.init_arr (JWord.W8.of_int 255)
                                           ) param_1 (BArray16.init_arr
                                                     (JWord.W8.of_int 255)) 
       param_0 (BArray16224.init_arr (JWord.W8.of_int 255)) param (
                                                            BArray48.init_arr
                                                            (JWord.W8.of_int 255))).
                                                              auto .
smt(BArray16.init_arrP BArray16224.init_arrP BArray48.init_arrP).
auto.
exfalso.
smt().
qed .
