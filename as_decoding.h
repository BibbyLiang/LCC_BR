#ifndef AS_DECODING_H
#define AS_DECODING_H

#include "cfg_decoding.h"

//#define K_M						S_MUL * (S_MUL - 1) * MESSAGE_LEN
#define LAYER_NUM				(MESSAGE_LEN + 1)
//#define LAYER_NUM				2
/*approximate and sufficient size allocation*/
#define C_SIZE					(S_MUL * (S_MUL + 1) * CODEWORD_LEN / 2)
//#define TERM_SIZE_Y				(((((sqrt(8 * C_SIZE / (MESSAGE_LEN - 1) + 1)) + 1) / 2) - 1) << 1)
//#define TERM_SIZE_Y				(8 * (S_MUL + 1))
//#define TERM_SIZE_X				((C_SIZE / ((TERM_SIZE_Y >> 0) + 1) + (TERM_SIZE_Y >> 0) / (MESSAGE_LEN - 1) / 2) << 1)
#define TERM_SIZE				((5 * (S_MUL + 1) * CODEWORD_LEN) / 6)//REAL_SIZE = TERM_SIZE^2
#define TERM_SIZE_Y				15
#define TERM_SIZE_X				TERM_SIZE
#if (0 == RECUR_RR)
#define POLY_NUM				TERM_SIZE_X * TERM_SIZE_Y * LAYER_NUM// notice there may be dangerous! POLY_NUM = ROOT_CNT_LAST_LAYER * GF_FIELD
#define ROOT_SIZE				POLY_NUM
#else
#define POLY_NUM				1// notice there may be dangerous! POLY_NUM = ROOT_CNT_LAST_LAYER * GF_FIELD
#define ROOT_SIZE				1
#endif

#if (1 == DEBUG_LOG)
extern FILE *frc_debug;
#endif

extern unsigned char output_polynomial[CODEWORD_LEN];
extern unsigned char decoded_codeword[CODEWORD_LEN];
extern unsigned char decoded_message[MESSAGE_LEN];

extern long long err_num;
extern unsigned char decoding_ok_flag;
extern long long weight_stored;
extern long long hamm_distance_debug;
extern long long rr_err;
extern long long max_dx, max_dy;
extern long long term_size_x, term_size_y;
extern unsigned char ***g_term_c_p;

extern unsigned char *g_term_c_expand;
extern unsigned char *tmp_g_term_c_expand;
extern unsigned char *mul_g_term_c_expand;
extern unsigned char *g_term_c_expand_store;

extern long long pow_val;
extern long long *cmplx_per_round_add;
extern long long *latency_per_round_add;
extern long long *cmplx_per_round_mul;
extern long long *latency_per_round_mul;

extern long long *skip_hist;
extern long long *pgd_hist;
extern long long *round_hist;

extern long long best_tst_vct_diff;
extern unsigned char intrplt_seq[CODEWORD_LEN];
#if 1//(1 == CFG_BR)
extern unsigned char *tst_vct_cmm;
#endif
extern unsigned char **tst_vct;
extern unsigned char tst_vct_debug[CODEWORD_LEN];

#if 1//(1 == CFG_IMD_STORE)
extern long long intp_cnt;
#endif

extern long long ml_tst_vct_recv_diff;
extern long long ml_tst_vct_enc_diff;

extern long long *g_term_x;
extern long long *g_term_y;
extern unsigned char **uncommon_term_c_choose;
extern unsigned char **uncommon_decoded_codeword;
extern long long term_size_p;

extern long long tv_round_clock_base;
extern long long tv_round_clock_base_prev;

#if (1 == CFG_ADAPTIVE_PARALLEL)
extern long long *adaptive_batch_num;
#endif

#if (1 == CFG_ADAPTIVE_SIZE_TEST)
extern long long adapive_size_br;
#endif

extern long long g_decoded_cnt;

#if (1 == CFG_NEW_TST_VCT)
extern unsigned char **new_tst_vct;
extern long long *new_tst_vct_seq;
#endif

extern long long satisfy_cnt;
extern long long new_tst_vct_ok_cnt;

extern clock_t start_t, stop_t;
extern float runtime_t;

extern int as_decoding();
extern int g_term_malloc();
extern int g_term_destroy();
extern int dfs_rr_recur(unsigned char *g_c_q,
					unsigned char *g_c_0_y,
					long long l);
extern long long hamm_distance_code_cal(unsigned char *a,
									  					  unsigned char *b,
									  					  long long len);
extern long long hamm_distance_bit_cal(unsigned char *a,
									  			  unsigned char *b,
									  			  long long len);
#if (1 == RE_ENCODING)
#if 1//(CFG_RR_MODE == BMA_RR)
extern int uncommon_dfs_rr_recur(unsigned char *g_c_q,
								  unsigned char *g_c_0_y,
								  long long m,
								  long long l);
extern int uncommon_check_rr_decoded_result_recur(unsigned char *msg,
														 long long l);								  
#endif
#if (CFG_RR_MODE == FAST_RR_M1)
extern int uncommon_fast_msg_get(long long l);
#endif
#endif

extern int chien_searching_for_g_0_y_recur(unsigned char *g_c_in, unsigned char root_test);
extern int g_term_0_y_cal_recur(unsigned char *g_c_in, unsigned char *g_c_out);
extern int g_term_new_gen_recur(unsigned char *g_c_in, unsigned char root_insert);
extern int fast_check_tst_vct_radius(long long dcd_cwd_idx, long long tst_vct_idx);
extern int store_q_poly_save(long long batch_idx, long long tst_vct_idx);
extern int store_q_poly_load(long long batch_idx, long long tst_vct_idx);
extern int bf_polynomial_process(unsigned char locator, unsigned char **poly, unsigned char **poly_back);
#if (1 == CFG_PRG_DECODING)
extern int MLcriterion(unsigned char est_cwd[]);
#endif
#if (1 == CFG_IMD_STORE)
int store_q_c_save(long long layer_idx, long long node_idx, long long tst_vct_idx);
int store_q_c_load(long long layer_idx, long long node_idx, long long tst_vct_idx);
#endif

#if (1 == CFG_ADAPTIVE_PARALLEL)
extern int adaptive_parallel_init();
#endif

#endif
