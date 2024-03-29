#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>
#include "cfg_decoding.h"
#include "debug_info.h"
#include "gf_cal.h"
#include "encoding.h"
#include "mod.h"
#include "rnd.h"
#include "as_decoding.h"
#include "re_encoding.h"
#include "br.h"

#define JUN_MA_EXAMPLE	0

unsigned char output_polynomial[CODEWORD_LEN] =
{
	0xFF,
	0xFF,
	0xFF,
	0xFF,
	0xFF,
	0xFF,
	0xFF
};

#if (1 == DEBUG_LOG)
FILE *frc_debug;
#endif

//unsigned char g_term_c[LAYER_NUM][POLY_NUM][term_size_x * term_size_y];
//long long g_term_x[term_size_x * term_size_y];
//long long g_term_y[term_size_x * term_size_y];
long long *g_term_x;
long long *g_term_y;

long long term_size_x = 0;
long long term_size_y = 0;
long long d_y_fix = 0;

#if (0 == RECUR_RR)
unsigned char g_term_0_y_c[LAYER_NUM][term_size_x * term_size_y];
unsigned char g_term_x_0_c[LAYER_NUM][term_size_x * term_size_y];
unsigned char f_root_val[ROOT_SIZE][ROOT_SIZE];
unsigned char f_root_prev[ROOT_SIZE][ROOT_SIZE];
long long f_root_cnt[ROOT_SIZE + 1];//used for next layer
#endif
long long sml_poly = 0xFF;
unsigned char decoded_codeword[CODEWORD_LEN];
unsigned char decoded_message[MESSAGE_LEN];
unsigned char tmp_message[MESSAGE_LEN];
unsigned char tmp_codeword[CODEWORD_LEN];
long long best_hamm_distance_code = 0x7FFF, best_hamm_distance_bit = 0x7FFF;

unsigned char ***g_term_c_p;
unsigned char g_term_phase = 0;

long long err_num = 0;
unsigned char decoding_ok_flag = 0;
long long weight_stored = 0;
long long hamm_distance_debug = 0x7FFF;
long long rr_err = 0;

long long max_dx = 0, max_dy = 0;

//unsigned char H_msg[MESSAGE_LEN + 1];

unsigned char intrplt_seq[CODEWORD_LEN];
unsigned char uncommon_place[YITA];

/*for un-common element interpolation*/
long long pow_val = (long long)(pow(2, YITA));
long long d_y_num = 0, term_size_p = 0;
unsigned char **uncommon_seq;//size: yita * (2^yita)
unsigned char **common_term_c_p;//size: m * (term_size)
long long *common_term_weight_pol;//size: m
long long *common_term_weight_pol_1_k_1;//size: m
long long *common_term_lexorder_pol;//size: m
long long common_l_s = 0, common_l_o = 0, common_l_w = 0;

unsigned char ***uncommon_term_c_p;//size: (2^yita) * m * (term_size)
unsigned char ***uncommon_table_c_prev;//size: (2^yita) * m * (term_size)
long long **uncommon_weight_pol;//size: (2^yita) * m
long long **uncommon_weight_pol_1_k_1;//size: (2^yita) * m
long long **uncommon_lexorder_pol;//size: (2^yita) * m
long long *uncommon_l_s, *uncommon_l_o, *uncommon_l_w;//size: (2^yita) 
unsigned char **uncommon_term_c_choose;//size: (2^yita) *(term_size)
unsigned char **uncommon_decoded_codeword;//size: (2^yita) * codewordlen
unsigned char **uncommon_decoded_message;
unsigned char **tst_vct;//size: (2^yita) * codewordlen
#if 1//(1 == CFG_BR)
unsigned char *tst_vct_cmm;
#endif
unsigned char tst_vct_debug[CODEWORD_LEN];
float *tst_vct_rel;

unsigned char first_tmp_message[MESSAGE_LEN];
long long **tst_vct_seq;
long long *decoded_tst_vct_seq;

#if (1 == CFG_STORE_PARALEL)
unsigned char ***store_uncommon_table_c_prev;//size: store_size * m * (term_size)
long long store_place = -1;
long long store_cnt = 0, store_cnt_prev = 0;
unsigned char *store_flag;
long long **store_group;
#endif

#if (1 == CFG_IMD_STORE)
unsigned char ****store_q_c_prev;//size: yita * 2^(yita) * m * term_size
unsigned char **store_q_c_flag;//size: yita * 2^(yita)
#endif
long long intp_cnt = 0;

long long *cmplx_per_round_add;
long long *latency_per_round_add;
long long *cmplx_per_round_mul;
long long *latency_per_round_mul;

long long *skip_hist;
long long *pgd_hist;
long long *round_hist;

long long best_tst_vct_diff = CODEWORD_LEN;

long long *adaptive_vct_seq;
unsigned char *adaptive_vct_seq_mark;
long long processed_tst_vct_num = 0;
#if (1 == CFG_ADAPTIVE_PARALLEL)
long long *adaptive_batch_num;
#endif
long long chnl_rel_thrd_cnt = 0;

long long ml_tst_vct_recv_diff = 0;
long long ml_tst_vct_enc_diff = 0;

long long tv_round_clock_base = 0;
long long tv_round_clock_base_prev = 0;

#if (1 == CFG_ADAPTIVE_SIZE_TEST)
long long adapive_size_br = 1;
#endif

long long g_decoded_cnt = 0;

#if (1 == CFG_NEW_TST_VCT)
unsigned char **new_tst_vct;
long long *new_tst_vct_seq;
long long new_tst_vct_cnt = 0;
long long *new_tst_vct_mark;
#endif

#if 1
long long symbol_err_cnt = 0;
long long replace_cnt = 0;
long long thr_cnt = 0;
long long satisfy_cnt = 0;
long long new_tst_vct_ok_cnt = 0;
#endif

clock_t start_t, stop_t;
float runtime_t = 0;

int poly_mul(unsigned char *a,
				unsigned char *b,
				unsigned char *product,
				long long len)
{
	long long i = 0, j = 0, k = 0;

	for(i = 0; i < len; i++)
	{
		if(a[i] != 0xFF)
		{
			for(j = 0; j < len; j++)
			{
				if(b[j] != 0xFF)
				{
					DEBUG_INFO("poly_product: %ld %ld %ld %x | %ld %ld %ld %x\n",
							   i,
							   g_term_x[i],
						       g_term_y[i],
						       a[i],
						       j,
						       g_term_x[j],
						       g_term_y[j],
						       b[j]);

					for(k = 0; k < len; k++)
					{
						if((g_term_x[k] == (g_term_x[i] + g_term_x[j]))
							&& (g_term_y[k] == (g_term_y[i] + g_term_y[j])))
						{
							product[k] = gf_add(product[k],
												gf_multp(a[i], b[j]));
						}
					}
				}
			}
		}
	}

	for(k = 0; k < len; k++)
	{
		if(0xFF != product[k])
		{
			DEBUG_INFO("poly_product: %ld %ld | %x\n",
				       g_term_x[k],
				       g_term_y[k],
				       product[k]);
		}
	}

	return 0;
}

int lex_order(long long **lex_table, long long d_x, long long d_y, long long y_weight)
{
	long long i = 0, j = 0, k = 0;
	long long max_degree = 0, min_degree = 0, degree_index = 0;
	long long tmp_lex_table[d_x][d_y];

	DEBUG_INFO("lex_order: %ld %ld\n", d_x, d_y);

	DEBUG_INFO("tmp_lex_table:\n");
	for(i = 0; i < d_x; i++)
	{
		for(j = 0; j < d_y; j++)
		{
#if 1
			tmp_lex_table[i][j] = 1 * i + y_weight * j;
#else//for test
			*((long long *)lex_table + i * d_y + j) = 1 * i + 1 * j;
#endif
			if(max_degree < tmp_lex_table[i][j])
			{
				max_degree = tmp_lex_table[i][j];
			}
			if(min_degree > tmp_lex_table[i][j])
			{
				min_degree = tmp_lex_table[i][j];
			}
			DEBUG_INFO("%ld ", tmp_lex_table[i][j]);
		}
		DEBUG_INFO("\n");
	}
	DEBUG_INFO("\n");

	DEBUG_INFO("max_degree: %ld\n", max_degree);
	DEBUG_INFO("min_degree: %ld\n", min_degree);

	for(k = min_degree; k <= max_degree; k++)
	{
#if(1 == RELEX_ORDER)
		for(j = 0; j < d_y; j++)
		{
			for(i = 0; i < d_x; i++)
#else
		for(i = 0; i < d_x; i++)
		{
			for(j = 0; j < d_y; j++)
#endif
			{
				if(k == tmp_lex_table[i][j])
				{
					*((long long *)lex_table + i * d_y + j) = degree_index;
					degree_index = degree_index + 1;
					//DEBUG_INFO("lex_table: %ld %ld %ld\n", k, degree_index, *((long long *)lex_table + i * d_y + j));
				}
			}
		}
	}

	DEBUG_INFO("ld table OK\n");		
}

int uncommon_place_init()
{
	long long i = 0, j = 0;

	for(i = 0; i < YITA; i++)
	{
		uncommon_place[i] = chnl_rel_order_idx[YITA - 1 - i];
		DEBUG_INFO("uncommon_place: %ld %ld\n", i, uncommon_place[i]);
	}
}

int intrplt_seq_init()
{
	long long i = 0, j = 0;

#if (1 == RE_ENCODING)
	for(i = 0; i < MESSAGE_LEN; i++)
	{
		intrplt_seq[i] = rel_group_seq[i];
	}
	for(i = 0; i < (CODEWORD_LEN - MESSAGE_LEN); i++)
	{
		intrplt_seq[i + MESSAGE_LEN] = unrel_group_seq[i];
	}
#else
	for(i = 0; i < CODEWORD_LEN; i++)
	{
		intrplt_seq[i] = power_polynomial_table[i + 1][0];
	}
#endif
	for(i = 0; i < CODEWORD_LEN; i++)
	{
		DEBUG_NOTICE("intrplt_seq: %ld %ld\n", i, intrplt_seq[i]);
	}
}

int interpolation_init()
{
	long long i = 0, j = 0, k = 0, m = 0, n = 0;
	long long a = 0, b = 0;
	long long tmp_sum = 0;
	unsigned char tmp_ff = 0xFF;
	long long l_s = 0x7FFF, l_o = 0x7FFF;;
	long long l_w = 0, tmp_real = 0;

	long long d_x = 0, d_y = 0, c = 0, term_num = 0, term_num_real = 0;
	long long d_x_max = 0, d_y_max = 0;

	for(i = 0; i < (CODEWORD_LEN + 1); i++)
	{
		for(j = 0; j < CODEWORD_LEN; j++)
		{
			tmp_sum = tmp_sum + mul_matrix[i][j] * (mul_matrix[i][j] + 1);
		}
	}
	c = tmp_sum / 2;

	d_x = term_size_x + 1;
	d_y = term_size_y + 1;

	long long lex_order_table[d_x][d_y];

	lex_order((long long **)lex_order_table, d_x, d_y, (MESSAGE_LEN - 1));
	//lex_order((long long **)lex_order_table, d_x, d_y, Y_WEIGHT);

	DEBUG_INFO("lex_order_table:\n");
	for(i = 0; i < d_x; i++)
	{
		for(j = 0; j < d_y; j++)
		{
			DEBUG_INFO("%ld ", lex_order_table[i][j]);
			if(c >= lex_order_table[i][j])
			{
				if(d_y_max < j)
				{
					d_y_max = j;
				}
			}
		}
		DEBUG_INFO("\n");
	}
	//test

	if(0 == d_y_fix)
	{
		d_y_fix = d_y_max;
	}
	else
	{
		d_y_max = d_y_fix;
	}

	DEBUG_INFO("d_y_max: %ld %ld %ld %ld %ld %ld\n",
			   c, d_x, d_y, d_y_max, term_size_x, term_size_y);

#if (1 == RE_ENCODING)
	lex_order((long long **)lex_order_table, d_x, d_y, Y_WEIGHT);
#endif

	d_x_max = d_x;
#if (0 == TERM_SIZE_DBG)	
	term_num_real = d_x * d_y;
#else	
	term_num_real = term_size_x * term_size_y;
#endif	

	/*use for un-common elements interpolation*/
	d_y_num = d_y_max + 1;
	term_size_p = term_num_real;
	
	common_term_c_p = (unsigned char**)malloc(sizeof(unsigned char*) * d_y_num);
	for(i = 0; i < d_y_num; i++)
	{
		common_term_c_p[i] = (unsigned char*)malloc(sizeof(unsigned char) * term_size_p);
  	}
  	for(i = 0; i < d_y_num; i++)
	{
		memset(common_term_c_p[i], 0xFF, sizeof(unsigned char) * term_size_p);
  	}
  	common_term_weight_pol = (long long*)malloc(sizeof(long long) * d_y_num);
  	common_term_weight_pol_1_k_1 = (long long*)malloc(sizeof(long long) * d_y_num);
  	common_term_lexorder_pol = (long long*)malloc(sizeof(long long) * d_y_num);

	return 0;
}

int koetter_interpolation()
{
	long long i = 0, j = 0, k = 0, m = 0, n = 0;
	long long a = 0, b = 0;
	long long tmp_sum = 0;
	unsigned char tmp_ff = 0xFF;
	long long l_s = 0x7FFF, l_o = 0x7FFF;;
	long long l_w = 0, tmp_real = 0;

	long long d_x = 0, d_y = 0, c = 0, term_num = 0, term_num_real = 0;
	long long d_x_max = 0, d_y_max = 0;
	unsigned char locator_seq[CODEWORD_LEN];

	for(i = 0; i < CODEWORD_LEN; i++)
	{
		locator_seq[i] = power_polynomial_table[i + 1][0];
	}

	for(i = 0; i < (CODEWORD_LEN + 1); i++)
	{
		for(j = 0; j < CODEWORD_LEN; j++)
		{
			tmp_sum = tmp_sum + mul_matrix[i][j] * (mul_matrix[i][j] + 1);
		}
	}
	c = tmp_sum / 2;
	//tmp_sum = pow((1 + 8 * (float)c / (MESSAGE_LEN - 1)), 0.5);
	//tmp_sum = (1 + ((long long)tmp_sum)) / 2;
	//d_y = (long long)(floor(tmp_sum));
	//d_y = floor((1 + (long long)pow((1 + 8 * (float)c / (MESSAGE_LEN - 1)), 0.5)) / 2);
	//d_x = floor(c / (d_y + 1) + d_y * (CODEWORD_LEN - MESSAGE_LEN - 1) / 2);

	//d_x = d_x << LEX_TABLE_EXPAND_SIZE;
	//d_y = d_y << LEX_TABLE_EXPAND_SIZE;
	//d_x = d_x * LEX_TABLE_EXPAND_SIZE;
	//d_y = d_y * LEX_TABLE_EXPAND_SIZE / 2;
	//d_y = d_y + 3;
	d_x = term_size_x + 1;
	d_y = term_size_y + 1;

	long long lex_order_table[d_x][d_y];

	lex_order((long long **)lex_order_table, d_x, d_y, (MESSAGE_LEN - 1));
	//lex_order((long long **)lex_order_table, d_x, d_y, Y_WEIGHT);

	DEBUG_INFO("lex_order_table:\n");
	for(i = 0; i < d_x; i++)
	{
		for(j = 0; j < d_y; j++)
		{
			DEBUG_INFO("%ld ", lex_order_table[i][j]);
			if(c >= lex_order_table[i][j])
			{
				if(d_y_max < j)
				{
					d_y_max = j;
				}
			}
		}
		DEBUG_INFO("\n");
	}
	//test
#if 0//(1 == RE_ENCODING)
	if(1 == S_MUL)
	{
		d_y_max = 1;
	}
	if(2 == S_MUL)
	{
		d_y_max = 2;
	}
	if(3 == S_MUL)
	{
		d_y_max = 3;
	}
#endif

	if(0 == d_y_fix)
	{
		d_y_fix = d_y_max;
	}
	else
	{
		d_y_max = d_y_fix;
	}

	DEBUG_INFO("d_y_max: %ld %ld %ld %ld %ld %ld\n",
	           c, d_x, d_y, d_y_max, term_size_x, term_size_y);
#if (1 == JUN_MA_EXAMPLE)
	d_y_max = 3;
#endif

#if 0
	for(i = 0; i < d_x; i++)
	{
		memset(lex_order_table[i], 0, sizeof(long long) * d_y);
	}
#endif
#if (1 == RE_ENCODING)
	lex_order((long long **)lex_order_table, d_x, d_y, Y_WEIGHT);
#endif

	d_x_max = d_x;
#if (0 == TERM_SIZE_DBG)	
	term_num_real = d_x * d_y;
#else	
	term_num_real = term_size_x * term_size_y;
#endif	

	/*use for un-common elements interpolation*/
	d_y_num = d_y_max + 1;
	term_size_p = term_num_real;
	common_term_c_p = (unsigned char**)malloc(sizeof(unsigned char*) * d_y_num);
	for(i = 0; i < d_y_num; i++)
	{
		common_term_c_p[i] = (unsigned char*)malloc(sizeof(unsigned char) * term_size_p);
  	}
  	for(i = 0; i < d_y_num; i++)
	{
		memset(common_term_c_p[i], 0xFF, sizeof(unsigned char) * term_size_p);
  	}
  	common_term_weight_pol = (long long*)malloc(sizeof(long long) * d_y_num);
  	common_term_weight_pol_1_k_1 = (long long*)malloc(sizeof(long long) * d_y_num);
  	common_term_lexorder_pol = (long long*)malloc(sizeof(long long) * d_y_num);

	DEBUG_INFO("constraint: %d %d %d %d %d %d %d %d\n", c, d_x, d_y, term_num_real, term_size_p, d_x_max, d_y_max, TERM_SIZE);
#if 0
	unsigned char g_table_c[d_y_max + 1][term_num];
	unsigned char g_table_x[term_num];
	unsigned char g_table_y[term_num];
	unsigned char discrepancy[d_y_max + 1];
	unsigned char weight_pol[d_y_max + 1];
	unsigned char tmp_table_c[term_num];
#endif
	unsigned char **g_table_c;
	unsigned char **g_table_c_prev;
	long long *g_table_x;
	long long *g_table_y;
	unsigned char *discrepancy;
	long long *weight_pol;
	long long *weight_pol_1_k_1;
	long long *lexorder_pol;
	unsigned char *tmp_table_c;
	long long *term_use_index;//malloc later

	g_table_c = (unsigned char**)malloc(sizeof(unsigned char*) * (d_y_max + 1));
	g_table_c_prev = (unsigned char**)malloc(sizeof(unsigned char*) * (d_y_max + 1));
	for (i = 0; i < (d_y_max + 1); i++)
	{
  		g_table_c[i] = (unsigned char*)malloc(sizeof(unsigned char) * term_num_real);
		g_table_c_prev[i] = (unsigned char*)malloc(sizeof(unsigned char) * term_num_real);
  	}
#if (0 == TERM_SIZE_DBG)  	
	g_table_x = (long long*)malloc(sizeof(long long) * term_num_real);
	g_table_y = (long long*)malloc(sizeof(long long) * term_num_real);
#endif	
	discrepancy = (unsigned char*)malloc(sizeof(unsigned char) * (d_y_max + 1));
	weight_pol = (long long*)malloc(sizeof(long long) * (d_y_max + 1));
	weight_pol_1_k_1 = (long long*)malloc(sizeof(long long) * (d_y_max + 1));
	lexorder_pol = (long long*)malloc(sizeof(long long) * (d_y_max + 1));
	tmp_table_c = (unsigned char*)malloc(sizeof(unsigned char) * term_num_real);

	for(i = 0; i < (d_y_max + 1); i++)
	{
		memset(g_table_c[i], 0xFF, sizeof(unsigned char) * term_num_real);
		memset(g_table_c_prev[i], 0xFF, sizeof(unsigned char) * term_num_real);
	}
#if (0 == TERM_SIZE_DBG)	
	memset(g_table_x, 0, sizeof(long long) * term_num_real);
	memset(g_table_y, 0, sizeof(long long) * term_num_real);
#endif	
	memset(discrepancy, 0xFF, sizeof(unsigned char) * (d_y_max + 1));
	memset(tmp_table_c, 0xFF, sizeof(unsigned char) * term_num_real);
	memset(weight_pol, -100, sizeof(long long) * (d_y_max + 1));
	memset(weight_pol_1_k_1, 0, sizeof(long long) * (d_y_max + 1));
	memset(lexorder_pol, 0x7FFF, sizeof(long long) * (d_y_max + 1));

	/*init (a, b) pairs*/
#if (0 == TERM_SIZE_DBG)
	k = 0;
	for(i = 0; i < (d_x + 0); i++)
	{
		for(j = 0; j < (d_y + 0); j++)
		{
			//if(S_MUL > (i + j))
			{
				g_table_x[k] = i;
				g_table_y[k] = j;
				DEBUG_NOTICE("g_table: %d %d %d\n", k, g_table_x[k], g_table_y[k]);
				k = k + 1;
			}
		}
	}
#else
	DEBUG_INFO("g_term init\n");
	g_table_x = (long long*)malloc(sizeof(long long) * (term_size_x * term_size_y));
	g_table_y = (long long*)malloc(sizeof(long long) * (term_size_x * term_size_y));
	memcpy(g_table_x, g_term_x, sizeof(long long) * (term_size_x * term_size_y));
	memcpy(g_table_y, g_term_y, sizeof(long long) * (term_size_x * term_size_y));
#endif

	for(i = 0; i <= d_y_max; i++)
	{
		for(j = 0; j < term_num_real; j++)
		{
#if (0 == JUN_MA_EXAMPLE)			
			if((0 == g_table_x[j]) && (i == g_table_y[j]))
			{
				g_table_c[i][j] = 0; //set coefficient of initial g to 1
				DEBUG_NOTICE("g_table_c: %d %d %x\n", i, j, g_table_c[i][j]);
				g_table_c_prev[i][j] = g_table_c[i][j];
				common_term_c_p[i][j] = g_table_c_prev[i][j];
				break;
			}
#else
			if(0 == i)
			{
				if((0 == g_table_x[j]) && (i == g_table_y[j]))
				{
					g_table_c[i][j] = 0; //set coefficient of initial g to 1
					DEBUG_NOTICE("g_table_c: %d | %d %d %x\n", i, g_table_x[j], g_table_y[j], g_table_c[i][j]);
					g_table_c_prev[i][j] = g_table_c[i][j];
					break;
				}
			}

			if(1 == i)
			{
				if((0 == g_table_x[j]) && (i == g_table_y[j]))
				{
					g_table_c[i][j] = 0; //set coefficient of initial g to 1
					DEBUG_NOTICE("g_table_c: %d | %d %d %x\n", i, g_table_x[j], g_table_y[j], g_table_c[i][j]);
					g_table_c_prev[i][j] = g_table_c[i][j];
					break;
				}
			}

			if(2 == i)
			{
				if((0 == g_table_x[j]) && (i == g_table_y[j]))
				{
					g_table_c[i][j] = 0x2; //set coefficient of initial g to 1
					DEBUG_NOTICE("g_table_c: %d | %d %d %x\n", i, g_table_x[j], g_table_y[j], g_table_c[i][j]);
					g_table_c_prev[i][j] = g_table_c[i][j];
				}
				if((1 == g_table_x[j]) && (i == g_table_y[j]))
				{
					g_table_c[i][j] = 0x0; //set coefficient of initial g to 1
					DEBUG_NOTICE("g_table_c: %d | %d %d %x\n", i, g_table_x[j], g_table_y[j], g_table_c[i][j]);
					g_table_c_prev[i][j] = g_table_c[i][j];
				}
			}

			if(3 == i)
			{
				if((0 == g_table_x[j]) && (i == g_table_y[j]))
				{
					g_table_c[i][j] = 0x5; //set coefficient of initial g to 1
					DEBUG_NOTICE("g_table_c: %d | %d %d %x\n", i, g_table_x[j], g_table_y[j], g_table_c[i][j]);
					g_table_c_prev[i][j] = g_table_c[i][j];
				}
				if((1 == g_table_x[j]) && (i == g_table_y[j]))
				{
					g_table_c[i][j] = 0x4; //set coefficient of initial g to 1
					DEBUG_NOTICE("g_table_c: %d | %d %d %x\n", i, g_table_x[j], g_table_y[j], g_table_c[i][j]);
					g_table_c_prev[i][j] = g_table_c[i][j];
				}
				if((2 == g_table_x[j]) && (i == g_table_y[j]))
				{
					g_table_c[i][j] = 0x1; //set coefficient of initial g to 1
					DEBUG_NOTICE("g_table_c: %d | %d %d %x\n", i, g_table_x[j], g_table_y[j], g_table_c[i][j]);
					g_table_c_prev[i][j] = g_table_c[i][j];
				}
				if((3 == g_table_x[j]) && (i == g_table_y[j]))
				{
					g_table_c[i][j] = 0x0; //set coefficient of initial g to 1
					DEBUG_NOTICE("g_table_c: %d | %d %d %x\n", i, g_table_x[j], g_table_y[j], g_table_c[i][j]);
					g_table_c_prev[i][j] = g_table_c[i][j];
				}
			}
#endif			
		}
	}

	for(i = 0; i < (d_y_max + 1); i++)
	{
		for(j = 0; j < term_num_real; j++)
		{
			if(0xFF != g_table_c[i][j])
			{
				if((weight_pol[i] < (g_table_x[j] + Y_WEIGHT * g_table_y[j]))
					|| ((weight_pol[i] == (g_table_x[j] + Y_WEIGHT * g_table_y[j]))
						&& (lexorder_pol[i] > lex_order_table[g_table_x[j]][g_table_y[j]])))
				{
					weight_pol[i] = (g_table_x[j] + Y_WEIGHT * g_table_y[j]);
					lexorder_pol[i] = lex_order_table[g_table_x[j]][g_table_y[j]];
				}
				DEBUG_INFO("pol_check: %d %d %d\n",
					        weight_pol[i],
					        lexorder_pol[i],
					        (g_table_x[j] + Y_WEIGHT * g_table_y[j]));
			}
		}
		common_term_weight_pol[i] = weight_pol[i];
		common_term_lexorder_pol[i] = lexorder_pol[i];
		common_term_weight_pol_1_k_1[i] = 0;
		DEBUG_INFO("pol: %d %d\n", weight_pol[i], lexorder_pol[i]);
	}

#if (1 == JUN_MA_EXAMPLE)
	for(j = 0; j < CODEWORD_LEN; j++) //for I, as 2^q - 1
	{
		for(i = 0; i < (CODEWORD_LEN + 1); i++)
		{
			beta_matrix[i][j] = 0xFF;
			if(0 == j)
			{
				beta_matrix[i][j] = 0xFF;
			}
			if(1 == j)
			{
				beta_matrix[i][j] = 0xFF;
			}
			if(2 == j)
			{
				beta_matrix[i][j] = 0x3;
			}
			if(3 == j)
			{
				beta_matrix[i][j] = 0x2;
			}
			if(4 == j)
			{
				beta_matrix[i][j] = 0xFF;
			}
			if(5 == j)
			{
				beta_matrix[i][j] = 0x1;
			}
			if(6 == j)
			{
				beta_matrix[i][j] = 0x0;
			}
		}
	}
	
	locator_seq[0] = 0x1;
	locator_seq[1] = 0x2;
	locator_seq[2] = 0x3;
	locator_seq[3] = 0x3;
	locator_seq[4] = 0x0;
	locator_seq[5] = 0x0;
	locator_seq[6] = 0x2;
#endif

#if 0
	for(j = 0; j < CODEWORD_LEN; j++) //for I, as 2^q - 1
#else
	for(j = 0; j < (CODEWORD_LEN - YITA); j++)
#endif
	{

#if (1 == RE_ENCODING)//skip reliable symbols
		unsigned char tmp_flag = 0;
		for(i = 0; i < MESSAGE_LEN; i++)
		{
			if(intrplt_seq[j] == rel_group_seq[i])
			{
				tmp_flag = 1;
				break;
			}
		}
		if(1 == tmp_flag)
		{
			continue;
		}
#endif
		
		for(i = 0; i < (CODEWORD_LEN + 1); i++)//for I, as n
		{
			
			if(0 == mul_matrix[i][intrplt_seq[j]])
			{
				continue;
			}

#if 0//this cannot work for no-re-encoding condition, there must be some reasons for that.
			if(0xFF == beta_matrix[i][j])
			{
				continue;
			}
#endif			

			DEBUG_INFO("-------------------------------------------\n");
			DEBUG_INFO("point: %d %d | %d %d | (%x %x)\n", CODEWORD_LEN, (CODEWORD_LEN + 1), i, intrplt_seq[j], locator_seq[intrplt_seq[j]], beta_matrix[i][intrplt_seq[j]]);

			/*the (a, b) pairs should be init here*/
			term_num = 0;//clear here
			for(m = 0; m < d_x; m++)
			{
				for(n = 0; n < d_y; n++)
				{
					if((mul_matrix[i][intrplt_seq[j]] - 1) >= (m + n))
					{
						term_num = term_num + 1;
					}
				}
			}

			DEBUG_NOTICE("term_num: %d\n", term_num);

			term_use_index = (long long*)malloc(sizeof(long long) * term_num);
			m = 0;
			for(k = 0; k < term_num_real; k++)
			{
				if((mul_matrix[i][intrplt_seq[j]] - 1) >= (g_table_x[k] + g_table_y[k]))
				{
					term_use_index[m] = k;
					DEBUG_NOTICE("term_use_index: %d | %d | %d %d\n", m, term_use_index[m], g_table_x[k], g_table_y[k]);
					m = m + 1;
				}
			}

			/*notice that only (a, b) pairs is constained by (a + b) < m directly.*/
			/*(r, s) pairs is related to the point (a, b), but not the constrain.*/
			for(k = 0; k < term_num; k++) //for II, as (a, b) pairs
			{
				DEBUG_NOTICE("*********************\n");
				DEBUG_NOTICE("k ready: %d %d | %d | (%d %d)\n", term_num, k, term_use_index[k], g_table_x[term_use_index[k]], g_table_y[term_use_index[k]]);
				memset(discrepancy, 0xFF, sizeof(unsigned char) * (d_y_max + 1));

				for(m = 0; m < (d_y_max + 1); m++) //for III, as Q_d_y_max
				{
					/*this itertation is used to calculate discrepancy and record l_s place*/
					tmp_sum = 0xFF;

					for(n = 0; n < term_num_real; n++) //for IV, as (r, s) pairs
					{
						if((g_table_x[n] < g_table_x[term_use_index[k]])
							|| (g_table_y[n] < g_table_y[term_use_index[k]])
							|| (0xFF == g_table_c_prev[m][n])
							|| ((0xFF == beta_matrix[i][intrplt_seq[j]]) && (g_table_y[n] != g_table_y[term_use_index[k]])))
						{
							continue;
						}

						DEBUG_NOTICE("++++++++++\n");
						DEBUG_NOTICE("(m, n) ready: %d (%d %d) %x\n", m, g_table_x[n], g_table_y[n], g_table_c_prev[m][n]);
						tmp_real = real_combine(g_table_x[n], g_table_x[term_use_index[k]]) * real_combine(g_table_y[n], g_table_y[term_use_index[k]]);
						//DEBUG_NOTICE("tmp_real: %d | %d %d %d | %d %d %d\n", tmp_real, g_table_x[n], g_table_x[term_use_index[k]], real_combine(g_table_x[n], g_table_x[term_use_index[k]]), g_table_y[n], g_table_y[term_use_index[k]], real_combine(g_table_y[n], g_table_y[term_use_index[k]]));
						tmp_ff = gf_real_mutp_ff(tmp_real, g_table_c_prev[m][n]);
						//DEBUG_NOTICE("tmp_ff: %x = %d mul %x\n", tmp_ff, tmp_real, g_table_c_prev[m][n]);
						//DEBUG_NOTICE("tmp_ff: %x * (%x = %x^%x)\n", tmp_ff, gf_pow_cal(power_polynomial_table[j + 1][0], (g_table_x[n] - g_table_x[term_use_index[k]])), power_polynomial_table[j + 1][0], (g_table_x[n] - g_table_x[term_use_index[k]]));
						tmp_ff = gf_multp(tmp_ff, gf_pow_cal(locator_seq[intrplt_seq[j]], (g_table_x[n] - g_table_x[term_use_index[k]])));
						//DEBUG_NOTICE("tmp_ff: %x * (%x = %x^%x)\n", tmp_ff, gf_pow_cal(beta_matrix[i][j], (g_table_y[n] - g_table_y[term_use_index[k]])), beta_matrix[i][j], (g_table_y[n] - g_table_y[term_use_index[k]]));
						tmp_ff = gf_multp(tmp_ff, gf_pow_cal(beta_matrix[i][intrplt_seq[j]], (g_table_y[n] - g_table_y[term_use_index[k]])));
						//DEBUG_NOTICE("gf_add: %x + %x\n", tmp_sum, tmp_ff);
						tmp_sum = gf_add(tmp_sum, tmp_ff);
#if (1 == CFG_DEBUG_NOTICE)						
						if(0xFF != tmp_sum)
						{
							DEBUG_NOTICE("tmp_sum: %d | %d\n", tmp_sum, tmp_ff);
						}
#endif						
					}
					
					if(0xFF != tmp_sum)
					{
						discrepancy[m] = tmp_sum;
						DEBUG_NOTICE("d: %d %d | %d %d | %d | %d\n", i, j, g_table_x[term_use_index[k]], g_table_y[term_use_index[k]], m, discrepancy[m]);
					}

					if(0xFF != discrepancy[m])
					{
						DEBUG_NOTICE("updating place center: %d | %d vs %d | %d vs %d\n", l_s, l_w, weight_pol[m], l_o, lexorder_pol[m]);
						if(((l_w > weight_pol[m])
								|| ((l_w == weight_pol[m])
									&& (l_o > lexorder_pol[m])))
							|| (0xFF == discrepancy[l_s]))
						{
							l_s = m;
							l_w = weight_pol[m];
							l_o = lexorder_pol[m];
							DEBUG_NOTICE("updated place center: %d | %d | %d\n", l_s, l_w, l_o);
						}
					}
				}

				DEBUG_NOTICE("l_s: %d\n", l_s);

				for(m = 0; m < (d_y_max + 1); m++)//update normal Q_l
				{
					if((m == l_s)
						|| (0xFF == discrepancy[m]))
					{
						continue;
					}

					for(n = 0; n < term_num_real; n++)
					{
						//g_table_c[m][n] = gf_multp(g_table_c_prev[m][n], discrepancy[l_s]);
						g_table_c[m][n] = gf_multp(g_table_c_prev[m][n], 0x0);
					}

					for(n = 0; n < term_num_real; n++)
					{
						tmp_table_c[n] = gf_multp(g_table_c_prev[l_s][n], discrepancy[m]);
						tmp_table_c[n] = gf_div(tmp_table_c[n], discrepancy[l_s]);
					}

					for(n = 0; n < term_num_real; n++)
					{
						g_table_c[m][n] = gf_add(g_table_c[m][n], tmp_table_c[n]);
					}
#if (1 == CFG_DEBUG_NOTICE)
					for(n = 0; n < term_num_real; n++)
					{
						if(0xFF != g_table_c[m][n])
						{
							DEBUG_NOTICE("Q_l: %d | %d %d | %x\n", m, g_table_x[n], g_table_y[n], g_table_c[m][n]);
						}
					}
#endif					
				}

				memset(tmp_table_c, 0xFF, sizeof(unsigned char) * term_num_real);
				for(n = 0; n < term_num_real; n++)//update Q_l_s
				{
					if(0xFF == discrepancy[l_s])
					{
						DEBUG_NOTICE("no update for this (a, b) pair: %d\n", l_s);
						break;
					}
					
					if(0xFF != g_table_c_prev[l_s][n])
					{
						//DEBUG_NOTICE("update Q_l_s: %d %d | %d %d | %x\n", l_s, n, g_table_x[n], g_table_y[n], g_table_c[l_s][n]);
						for(m = 0; m < term_num_real; m++)
						{
							//DEBUG_NOTICE("checking m: %d | %d %d | %x\n", m, g_table_x[m], g_table_y[m], g_table_c[l_s][m]);
							if((g_table_x[m] == (g_table_x[n] + 1))
								&& (g_table_y[m] == g_table_y[n]))
							{
								tmp_table_c[m] = gf_add(g_table_c_prev[l_s][n], tmp_table_c[m]);
								//DEBUG_NOTICE("update tmp_table_c[m]: %d %d | %d %d | %x\n", m, n, g_table_x[m], g_table_y[m], tmp_table_c[m]);
								break;
							}
						}

						tmp_table_c[n] = gf_add(gf_multp(g_table_c_prev[l_s][n], locator_seq[intrplt_seq[j]]), tmp_table_c[n]);
					}
				}
				for(n = 0; n < term_num_real; n++)
				{
					if(0xFF == discrepancy[l_s])
					{
						DEBUG_NOTICE("no update for this (a, b) pair: %d\n", l_s);
						break;
					}

					g_table_c[l_s][n] = 0xFF;

					if(0xFF != tmp_table_c[n])
					{
						//g_table_c[l_s][n] = gf_multp(tmp_table_c[n], discrepancy[l_s]);
						//g_table_c[l_s][n] = gf_multp(tmp_table_c[n], 0x0);
						g_table_c[l_s][n] = tmp_table_c[n];
						DEBUG_NOTICE("Q_l_s_c: %d | %d %d | %x\n", l_s, g_table_x[n], g_table_y[n], g_table_c[l_s][n]);
					}
				}

				for(m = 0; m < (d_y_max + 1); m++)
				{
					weight_pol[m] = -100;
					lexorder_pol[m] = 0x7FFF;

					weight_pol_1_k_1[m] = 0;
					
					for(n = 0; n < term_num_real; n++)
					{
						if(0xFF != g_table_c[m][n])
						{
							if((weight_pol[m] < (g_table_x[n] + Y_WEIGHT * g_table_y[n]))
								|| ((weight_pol[m] == (g_table_x[n] + Y_WEIGHT * g_table_y[n])) 
									&& (lexorder_pol[m] > lex_order_table[g_table_x[n]][g_table_y[n]])))
							{
								weight_pol[m] = (g_table_x[n] + Y_WEIGHT * g_table_y[n]);
								lexorder_pol[m] = lex_order_table[g_table_x[n]][g_table_y[n]];
								if((g_table_x[n] >= d_x)
									|| (g_table_y[n] >= d_y))
								{
									DEBUG_IMPOTANT("lex_order_table_err: %ld | %ld %ld | %ld %ld | %ld\n",
												   n,
										           g_table_x[n],
										           g_table_y[n],
										           d_x,
										           d_y,
										           lexorder_pol[m]);
								}
								DEBUG_NOTICE("pol_updating: %d %d\n", weight_pol[m], lexorder_pol[m]);
							}

							if((weight_pol_1_k_1[m] < (g_table_x[n] + (MESSAGE_LEN - 1) * g_table_y[n]))
								|| ((weight_pol_1_k_1[m] == (g_table_x[n] + (MESSAGE_LEN - 1) * g_table_y[n])) 
									&& (lexorder_pol[m] > lex_order_table[g_table_x[n]][g_table_y[n]])))
							{
								weight_pol_1_k_1[m] = (g_table_x[n] + (MESSAGE_LEN - 1) * g_table_y[n]);
								lexorder_pol[m] = lex_order_table[g_table_x[n]][g_table_y[n]];
								if((g_table_x[n] >= d_x)
									|| (g_table_y[n] >= d_y))
								{
									DEBUG_IMPOTANT("lex_order_table_err: %ld | %ld %ld | %ld %ld | %ld\n",
												   n,
										           g_table_x[n],
										           g_table_y[n],
										           d_x,
										           d_y,
										           lexorder_pol[m]);
								}
								DEBUG_NOTICE("pol_updating_1-k-1: %d %d\n", weight_pol_1_k_1[m], lexorder_pol[m]);
							}

							/*update for common element*/
							if((CODEWORD_LEN - YITA) > j)
							{
								common_term_weight_pol[m] = weight_pol[m];
								common_term_weight_pol_1_k_1[m] = weight_pol_1_k_1[m];
								common_term_lexorder_pol[m] = lexorder_pol[m];
							}
						}
					}
					DEBUG_NOTICE("pol: %d %d %d %d\n", m, weight_pol[m], lexorder_pol[m], weight_pol_1_k_1[m]);
				}
				l_w = weight_pol[l_s];
				l_o = lexorder_pol[l_s];
				if((CODEWORD_LEN - YITA) > j)
				{
					common_l_s = l_s;
					common_l_w = l_w;
					common_l_o = l_o;
				}

				/*store g as prev_poly*/
				for(m = 0; m < (d_y_max + 1); m++)
				{
					for(n = 0; n < term_num_real; n++)
					{
						g_table_c_prev[m][n] = g_table_c[m][n];
						if((CODEWORD_LEN - YITA) > j)
						{
							common_term_c_p[m][n] = g_table_c_prev[m][n];
						}
#if (1 == CFG_DEBUG_NOTICE)						
						if(0xFF != g_table_c_prev[m][n])
						{
							DEBUG_NOTICE("g_table_c_prev: %d | %d %d | %d %d | %d\n",
								          m,
								          lex_order_table[g_table_x[n]][g_table_y[n]],
								          (g_table_x[n] + (MESSAGE_LEN - 1) * g_table_y[n]),
								          g_table_x[n],
								          g_table_y[n],
								          g_table_c_prev[m][n]);
						}
#endif

						if(0xFF != g_table_c_prev[m][n])
						{
							if(g_table_x[n] > max_dx)
							{
								max_dx = g_table_x[n];
								//DEBUG_SYS("max_dx: %ld\n", max_dx);
							}
							if(g_table_y[n] > max_dy)
							{
								max_dy = g_table_y[n];
								//DEBUG_SYS("max_dy: %ld\n", max_dy);
							}
						}
					}
				}
			}

			free(term_use_index);
			term_use_index = NULL;
		}
	}
#if 0
	/*find the place of smallest polynomial*/
	tmp_real = 0x7FFF;//notice this, it should be init large enough
	for(m = 0; m < (d_y_max + 1); m++)
	{
		if(tmp_real > weight_pol[m])
		{
			DEBUG_NOTICE("sml_updated: %d | %d %d | %d\n", m, tmp_real, weight_pol[m], lexorder_pol[m]);
			sml_poly = m;
			tmp_real = weight_pol[m];
		}
		if((tmp_real == weight_pol[m])
			&& (lexorder_pol[sml_poly] > lexorder_pol[m]))
		{
			DEBUG_NOTICE("sml_updated: %d | %d %d | %d\n", m, tmp_real, weight_pol[m], lexorder_pol[m]);
			sml_poly = m;
		}
	}

	/*copy the interpolated polynomials to global memory*/
	for(n = 0; n < term_num_real; n++)
	{
		if(0xFF != g_table_c[sml_poly][n])
		{
			for(k = 0; k < (term_size_x * term_size_y); k++)
			{
				if((g_table_x[n] == g_term_x[k])
					&& (g_table_y[n] == g_term_y[k]))
				{
					g_term_c_p[g_term_phase][0][k] = g_table_c[sml_poly][n];
					DEBUG_IMPOTANT("g_term: %d %d | %d %d | %x\n", 
														k,
														sml_poly,
														g_term_x[k],
														g_term_y[k],
														g_term_c_p[g_term_phase][0][k]);
					break;
				}
			}
		}
	}
#endif
#if 0
/*for re-encoding test(polynomial calculating method)*/
#if (CFG_RR_MODE >= CONV_RE_ENC_SYS)
	unsigned char tmp_product[term_size_x * term_size_y];
	unsigned char tmp_v[term_size_x * term_size_y];
	unsigned char tmp_q0[term_size_x * term_size_y];
	unsigned char tmp_q1[term_size_x * term_size_y];
	memset(tmp_product, 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));
	memset(tmp_v, 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));
	memset(tmp_q0, 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));
	memset(tmp_q1, 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));

	j = 0;
	for(i = 0; i < (term_size_x * term_size_y); i++)
	{
		if(j == g_term_x[i])
		{
			tmp_v[i] = v[j];
			j++;
		}
		if(j >= (MESSAGE_LEN + 1))
		{
			break;
		}
	}

	for(i = 0; i < (term_size_x * term_size_y); i++)
	{
		if((0xFF != g_term_c_p[g_term_phase][0][i])
			&& (0 == g_term_y[i]))
		{
			tmp_q0[i] = g_term_c_p[g_term_phase][0][i];
		}
	}

	for(i = 0; i < (term_size_x * term_size_y); i++)
	{
		if((0xFF != g_term_c_p[g_term_phase][0][i])
			&& (0 != g_term_y[i]))
		{
			tmp_q1[i] = g_term_c_p[g_term_phase][0][i];
		}
	}

	poly_mul(tmp_q0,
		     tmp_v,
		     tmp_product,
		     term_size_x * term_size_y);

	for(i = 0; i < (term_size_x * term_size_y); i++)
	{
		if(0 != g_term_y[i])
		{
			tmp_product[i] = gf_add(tmp_product[i], g_term_c_p[g_term_phase][0][i]);
		}
		if(0xFF != tmp_product[i])
		{
			DEBUG_NOTICE("tmp_product: %ld %ld | %x\n",
				         g_term_x[i],
				         g_term_y[i],
				         tmp_product[i]);

			if(g_term_x[i] > max_dx)
			{
				max_dx = g_term_x[i];
				//DEBUG_SYS("max_dx: %ld\n", max_dx);
			}
			if(g_term_y[i] > max_dy)
			{
				max_dy = g_term_y[i];
				//DEBUG_SYS("max_dy: %ld\n", max_dy);
			}
		}
	}
	memcpy(g_term_c_p[g_term_phase][0], tmp_product, sizeof(unsigned char) * (term_size_x * term_size_y));

#if (CFG_RR_MODE == CONV_RE_ENC)//Norma; RR for EVA Enc
	unsigned char L[MESSAGE_LEN][MESSAGE_LEN + 1];
	memset(H_msg, 0xFF, sizeof(unsigned char) * (MESSAGE_LEN + 1));
	for(i = 0; i < MESSAGE_LEN; i++)
	{
		l_cal(rel_group_seq[i], L[i]);
	}
	for(i = 0; i < MESSAGE_LEN; i++)
	{
		for(j = 0; j < (MESSAGE_LEN + 1); j++)
		{
			L[i][j] = gf_multp(L[i][j], received_polynomial[rel_group_seq[i]]);
		}
	}
	for(i = 0; i < MESSAGE_LEN; i++)
	{
		for(j = 0; j < (MESSAGE_LEN + 1); j++)
		{
			H_msg[j] = gf_add(H_msg[j], L[i][j]);
		}
	}
	for(i = 0; i < (MESSAGE_LEN + 1); i++)
	{
		DEBUG_NOTICE("H: %d | %x\n", i, H_msg[i]);
	}
#endif

#if (CFG_RR_MODE == CONV_RE_ENC_IDFT)//IDFT
	unsigned char inv_val = 0xFF;
	for(i = 0; i < (MESSAGE_LEN + 1); i++)
	{
		inv_val = gf_div(0x0, power_polynomial_table[i + 1][0]);
		H_msg[i] = poly_eva(phi, CODEWORD_LEN, inv_val);
		DEBUG_NOTICE("H: %d | %x\n", i, H_msg[i]);
	}
#if 0	
	unsigned char tmp_poly[CODEWORD_LEN] = {0x5, 0xFF, 0x2, 0x4, 0x1, 0x4, 0x4};
	val = poly_eva(tmp_poly, CODEWORD_LEN, 0x0);
	DEBUG_NOTICE("val: %x\n", val);
	val = poly_eva(tmp_poly, CODEWORD_LEN, 0x6);
	DEBUG_NOTICE("val: %x\n", val);
	val = poly_eva(tmp_poly, CODEWORD_LEN, 0x5);
	DEBUG_NOTICE("val: %x\n", val);
	val = poly_eva(tmp_poly, CODEWORD_LEN, 0x4);
	DEBUG_NOTICE("val: %x\n", val);
	val = poly_eva(tmp_poly, CODEWORD_LEN, 0x3);
	DEBUG_NOTICE("val: %x\n", val);
#endif	
#endif

#if 0//fast message getting for m=1
	unsigned char q0[CODEWORD_LEN], q1[CODEWORD_LEN];
	memset(q0, 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
	memset(q1, 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
	unsigned char q0_dev[CODEWORD_LEN], q1_dev[CODEWORD_LEN], v_dev[MESSAGE_LEN + 1];
	memset(q0_dev, 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
	memset(q1_dev, 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
	memset(v_dev, 0xFF, sizeof(unsigned char) * (MESSAGE_LEN + 1));
	for(i = 0; i < (term_size_x * term_size_y); i++)
	{
		if(0xFF != tmp_q0[i])
		{
			DEBUG_NOTICE("q0: %d %d| %x\n", g_term_x[i], g_term_y[i], tmp_q0[i]);
			q0[g_term_x[i]] = tmp_q0[i];
		}
	}
	for(i = 0; i < (term_size_x * term_size_y); i++)
	{
		if(0xFF != tmp_q1[i])
		{
			DEBUG_NOTICE("q1: %d %d| %x\n", g_term_x[i], g_term_y[i], tmp_q1[i]);
			q1[g_term_x[i]] = tmp_q1[i];
		}
	}
	for(i = 0; i < CODEWORD_LEN; i++)
	{
		DEBUG_NOTICE("q: %ld | %x %x\n", i, q0[i], q1[i]);
	}
	unsigned char rec_dir_cw[CODEWORD_LEN];
	memset(rec_dir_cw, 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
	unsigned char v_val = 0xFF, q1_val = 0xFF, q0_val = 0xFF;
	for(i = 0; i < CODEWORD_LEN; i++)
	{
		q0_val = poly_eva(q0,
			              CODEWORD_LEN,
			              power_polynomial_table[i + 1][0]);
		v_val = poly_eva(v,
			             (MESSAGE_LEN + 1),
			             power_polynomial_table[i + 1][0]);
		q1_val = poly_eva(q1,
		                  CODEWORD_LEN,
		                  power_polynomial_table[i + 1][0]);
		if(0xFF != q1_val)
		{
			rec_dir_cw[i] = gf_div(gf_multp(q0_val, v_val),
								   q1_val);
		}
		else//there are some problems now
		{
			for(j = 0; j < CODEWORD_LEN; j++)
			{
				if(0 != (j % 2))
				{
					q1_dev[j - 1] = q1[j];
				}
				else
				{
					q1_dev[j - 1] = 0xFF;
				}
			}
			q1_val = poly_eva(q1_dev,
			                  CODEWORD_LEN,
			              	  power_polynomial_table[i + 1][0]);
			
			if(0xFF == v_val)
			{
				for(j = 1; j < (MESSAGE_LEN + 1); j++)
				{
					if(0 != (j % 2))
					{
						v_dev[j - 1] = v[j];
					}
					DEBUG_NOTICE("v_dev: %ld | %x\n", j - 1, v_dev[j - 1]);
				}

				v_val = poly_eva(v_dev,
			             		 (MESSAGE_LEN + 1),
			             		 power_polynomial_table[i + 1][0]);

				rec_dir_cw[i] = gf_div(gf_multp(q0_val, v_val),
								       q1_val);
			}

			if(0xFF == q0_val)
			{
				for(j = 1; j < (MESSAGE_LEN + 1); j++)
				{
					if(0 != (j % 2))
					{
						q0_dev[j - 1] = q0[j];
					}
					DEBUG_NOTICE("q0_dev: %ld | %x\n", j - 1, q0_dev[j - 1]);
				}

				q0_val = poly_eva(q0_dev,
			             		 CODEWORD_LEN,
			             		 power_polynomial_table[i + 1][0]);

				rec_dir_cw[i] = gf_div(gf_multp(q0_val, v_val),
								       q1_val);
			}
		}

		DEBUG_NOTICE("rec_dir_cw: %d | %x*%x/%x=%x | %x\n",
			         i,
			         v_val,
			         q0_val,
			         q1_val,
			         rec_dir_cw[i],
			         gf_add(rec_dir_cw[i], phi[i]));
	}
#endif	
#endif

#if 0
	g_term_c_p[g_term_phase][0][1] = 0xFF;
	g_term_c_p[g_term_phase][0][4] = 0xFF;
	g_term_c_p[g_term_phase][0][7] = 0xFF;
	for(k = 0; k < (term_size_x * term_size_y); k++)
	{
		if((1 == g_term_x[k])
			&& (2 == g_term_y[k]))
		{
			g_term_c_p[g_term_phase][0][k] = 0x3;
		}
		if((0 == g_term_x[k])
			&& (1 == g_term_y[k]))
		{
			g_term_c_p[g_term_phase][0][k] = 0x6;
		}
		if((0 == g_term_x[k])
			&& (2 == g_term_y[k]))
		{
			g_term_c_p[g_term_phase][0][k] = 0x5;
		}
	}
#endif
#endif
#if 0
	/*Debug Criterion for GS Decoding*/
	if((S_MUL * (CODEWORD_LEN - err_num)) > weight_pol_1_k_1[sml_poly])
	{
		DEBUG_NOTICE("decoding_ok_flag: %d %d %d\n",
			         decoding_ok_flag,
			         (S_MUL * (CODEWORD_LEN - err_num)),
			         weight_pol_1_k_1[sml_poly]);
		if(0 == decoding_ok_flag)
		{
			decoding_ok_flag = 1;
			DEBUG_NOTICE("decoding_ok_flag = 1!\n");
		}
		weight_stored = weight_pol_1_k_1[sml_poly];
	}
#endif
	/*free resources*/
	for(i = 0; i < (d_y_max + 1); i++)
	{
  		free(g_table_c[i]);
		g_table_c[i] = NULL;

		free(g_table_c_prev[i]);
		g_table_c_prev[i] = NULL;
  	}
	free(g_table_c);
	g_table_c = NULL;
	free(g_table_c_prev);
	g_table_c_prev = NULL;
	free(g_table_x);
	g_table_x = NULL;
	free(g_table_y);
	g_table_y = NULL;
	free(discrepancy);
	discrepancy = NULL;
	free(weight_pol);
	weight_pol = NULL;
	free(weight_pol_1_k_1);
	weight_pol_1_k_1 = NULL;
	free(lexorder_pol);
	lexorder_pol = NULL;
	free(tmp_table_c);
	tmp_table_c = NULL;

	return 0;
}

#if (1 == CFG_NEW_TST_VCT)
int new_tst_vct_init()
{
	long long i = 0, j = 0;
	/*increase pow_val test-vectors*/
	new_tst_vct = (unsigned char**)malloc(sizeof(unsigned char*) * pow_val);
	for(i = 0; i < pow_val; i++)
	{
		new_tst_vct[i] = (unsigned char*)malloc(sizeof(unsigned char) * CODEWORD_LEN);
  	}
  	for(i = 0; i < pow_val; i++)
	{
		memcpy(new_tst_vct[i], tst_vct[i], sizeof(unsigned char) * CODEWORD_LEN);
		new_tst_vct[i][chnl_rel_order_idx[YITA]] = power_polynomial_table[chnl_rel_scd_id[chnl_rel_order_idx[YITA]]][0];
		DEBUG_NOTICE("new_tst_vct_gen: %ld %ld | %ld | %x\n", i, chnl_rel_order_idx[YITA], tst_vct[i][chnl_rel_order_idx[YITA]], chnl_rel_scd_id[chnl_rel_order_idx[YITA]]);
  	}

  	new_tst_vct_seq = (long long*)malloc(sizeof(long long) * pow_val);
	for(i = pow_val; i < (pow_val + pow_val); i++)
	{
		new_tst_vct_seq[i - pow_val] = i;
	}
	
	for(i = 0; i < pow_val; i++)
	{
		for(j = 0; j < CODEWORD_LEN; j++)
		{
			DEBUG_NOTICE("new_tst_vct: %ld %ld | %ld | %x\n", i, j, new_tst_vct_seq[i], new_tst_vct[i][j]);
		}
	}
	
	new_tst_vct_cnt = 0;
	
	new_tst_vct_mark = (long long*)malloc(sizeof(long long) * pow_val);
	memset(new_tst_vct_mark, 0, sizeof(long long) * pow_val);

	return 0;
}

int new_tst_vct_exit()
{
	long long i = 0;

	for(i = 0; i < pow_val; i++)
	{
		free(new_tst_vct[i]);
		new_tst_vct[i] = NULL;
	}
	free(new_tst_vct);
	new_tst_vct = NULL;

	free(new_tst_vct_seq);
	new_tst_vct_seq = NULL;
	
	free(new_tst_vct_mark);
	new_tst_vct_mark = NULL;

	return 0;
}
#endif

#if (1 == CFG_ADAPTIVE_PARALLEL)
int adaptive_parallel_init()
{
	long long i = 0, j = 0;
	long long vct_cnt = 0, vct_inc = 0;
	long long all_seq[pow_val];
	float all_chnl_rel[pow_val];

	adaptive_batch_num = (long long*)malloc(sizeof(long long) * pow_val);

	for(i = 0; i < pow_val; i++)
	{
		all_seq[i] = i;
	}
	memcpy(all_chnl_rel, tst_vct_rel, sizeof(float) * pow_val);
	BubbleSort5(all_chnl_rel, pow_val, all_seq);
	for(i = 0; i < pow_val; i++)
	{
		DEBUG_INFO("all_rel_sort: %ld | %f | %ld\n",
		           i,
		           all_chnl_rel[i],
		           all_seq[i]);
	}
	memcpy(adaptive_vct_seq, all_seq, sizeof(long long) * pow_val);
	
	vct_cnt = 0;
	for(i = 0; i < pow_val; i++)
	{
		if(pow_val <= vct_cnt)
		{
			adaptive_batch_num[i] = 0;
			continue;
		}
#if 1
		if(YITA >= (i * 0))
		{
			vct_inc = (long long)pow(2, i * 3);//notice this!!!
		}
#else
		if(pow_val >= chnl_rel_thrd_cnt)
		{
			if((0 != chnl_rel_thrd_cnt)
				&& (1 == i))
			{
				vct_inc = chnl_rel_thrd_cnt;
			}
			else if(0 == i)
			{
				vct_inc = 1;
			}
			else
			{
				vct_inc = CFG_ADAPTIVE_SIZE;
			}
		}
#endif
		else
		{
			vct_inc = pow_val;
		}

#if 1
		if(CFG_ADAPTIVE_SIZE < vct_inc)
		{
			vct_inc = CFG_ADAPTIVE_SIZE;
		}
#endif
#if (1 == CFG_ADAPTIVE_SIZE_TEST)
		if(adapive_size_br < vct_inc)
		{
			vct_inc = adapive_size_br;
		}
#endif
		
		if(vct_inc < (pow_val - vct_cnt))
		{	
			adaptive_batch_num[i] = vct_inc;
			vct_cnt = vct_cnt + vct_inc;
		}
		else
		{
			adaptive_batch_num[i] = pow_val - vct_cnt;
			vct_cnt = pow_val;
		}
		DEBUG_INFO("adaptive_batch_num: %ld | %ld\n",
		           i,
		           adaptive_batch_num[i]);
	}

#if 0//a special strategy
	adaptive_batch_num[0] = 1;
	adaptive_batch_num[1] = pow_val - 1;
	for(i = 2; i < pow_val; i++)
	{
		adaptive_batch_num[i] = 0;
	}
#endif

	vct_cnt = 0;
	for(i = 0; i < pow_val; i++)//round
	{
		for(j = 0; j < pow_val; j++)//batch
		{
			if(j < adaptive_batch_num[i])
			{
				tst_vct_seq[j][i] = adaptive_vct_seq[vct_cnt];
				vct_cnt++;
			}
			else
			{
				tst_vct_seq[j][i] = -1;
			}
			DEBUG_INFO("adaptive_tst_vct_seq: %ld %ld | %ld\n",
			           j,
			           i,
			           tst_vct_seq[j][i]);
		}
	}

	return 0;
}

int adaptive_parallel_exit()
{
	long long i = 0, j = 0;
	
	DEBUG_INFO("%s\n", __func__);

	free(adaptive_batch_num);
	adaptive_batch_num = NULL;

	return 0;
}
#endif

int uncommon_interpolation_init()
{
	long long i = 0, j = 0, k = 0;
	long long tmp_cnt = 0;
	unsigned char tmp_flag = 1, tmp_idx = 0;

	/*init un-common elements interpolating points*/
	uncommon_seq = (unsigned char**)malloc(sizeof(unsigned char*) * YITA);
	for(i = 0; i < YITA; i++)
	{
		uncommon_seq[i] = (unsigned char*)malloc(sizeof(unsigned char) * (pow_val));
  	}
	for(i = 0; i < YITA; i++)
	{
		tmp_cnt = pow_val / ((long long)(pow(2, (i + 1))));
		for(j = 0; j < pow_val; j++)
		{
			if(0 == (j % (tmp_cnt)))
			{
				if(1 == tmp_flag)
				{
					tmp_flag = 0;
				}
				else
				{
					tmp_flag = 1;
				}
			}
			DEBUG_NOTICE("tmp_flag: %ld %ld %ld %ld\n",
			             i,
			             j,
			             tmp_cnt,
			             tmp_flag);

			if(0 == tmp_flag)
			{
				tmp_idx = chnl_rel_max_id[uncommon_place[i]];
				//uncommon_seq[i][j] = power_polynomial_table[tmp_idx][0];
				uncommon_seq[i][j] = tmp_idx;
			}
			if(1 == tmp_flag)
			{
				tmp_idx = chnl_rel_scd_id[uncommon_place[i]];
				//uncommon_seq[i][j] = power_polynomial_table[tmp_idx][0];
				uncommon_seq[i][j] = tmp_idx;
			}

			DEBUG_NOTICE("uncommon_seq: %ld %ld %ld %ld %ld\n",
			             i,
			             j,
			             uncommon_place[i],
			             tmp_idx,
			             uncommon_seq[i][j]);
		}
	}

#if (0 == CFG_BR)
	/*init un-common elements interpolating Q*/
	uncommon_term_c_p = (unsigned char***)malloc(sizeof(unsigned char**) * pow_val);
	for (i = 0; i < pow_val; i++)
	{
  		uncommon_term_c_p[i] = (unsigned char**)malloc(sizeof(unsigned char*) * d_y_num);

		for(j = 0; j < d_y_num; j++)
		{
			uncommon_term_c_p[i][j] = (unsigned char*)malloc(sizeof(unsigned char) * term_size_p);
		}
  	}
  	for(i = 0; i < pow_val; i++)
  	{
  		for(j = 0; j < d_y_num; j++)
  		{
  			memcpy(uncommon_term_c_p[i][j], common_term_c_p[j], sizeof(unsigned char) * term_size_p);
  		}
  	}
#if (1 == CFG_DEBUG_NOTICE)  	
  	for(i = 0; i < pow_val; i++)
  	{
  		for(j = 0; j < d_y_num; j++)
  		{
  			for(k = 0; k < term_size_p; k++)
  			{
  				if(0xFF != uncommon_term_c_p[i][j][k])
  				{
  					DEBUG_NOTICE("uncommon_term_c_p: %ld %ld %ld %x\n",
  					             i,
  					             j,
  					             k,
  					             uncommon_term_c_p[i][j][k]);
  				}
  			}
  		}
  	}
#endif	
  	
  	/*init un-common elements interpolating Q for storage*/
  	uncommon_table_c_prev = (unsigned char***)malloc(sizeof(unsigned char**) * pow_val);
	for (i = 0; i < pow_val; i++)
	{
  		uncommon_table_c_prev[i] = (unsigned char**)malloc(sizeof(unsigned char*) * d_y_num);

		for(j = 0; j < d_y_num; j++)
		{
			uncommon_table_c_prev[i][j] = (unsigned char*)malloc(sizeof(unsigned char) * term_size_p);
		}
  	}
  	for(i = 0; i < pow_val; i++)
  	{
  		for(j = 0; j < d_y_num; j++)
  		{
  			//memset(uncommon_table_c_prev[i][j], 0xFF, sizeof(unsigned char) * term_size_p);
  			memcpy(uncommon_table_c_prev[i][j], uncommon_term_c_p[i][j], sizeof(unsigned char) * term_size_p);
  		}
  	}

	/*init weight_pol*/
	uncommon_weight_pol = (long long**)malloc(sizeof(long long*) * pow_val);
	uncommon_weight_pol_1_k_1 = (long long**)malloc(sizeof(long long*) * pow_val);
	uncommon_lexorder_pol = (long long**)malloc(sizeof(long long*) * pow_val);
	for(i = 0; i < pow_val; i++)
	{
		uncommon_weight_pol[i] = (long long*)malloc(sizeof(long long) * d_y_num);
		uncommon_weight_pol_1_k_1[i] = (long long*)malloc(sizeof(long long) * d_y_num);
		uncommon_lexorder_pol[i] = (long long*)malloc(sizeof(long long) * d_y_num);
  	}
  	for(i = 0; i < pow_val; i++)
  	{
  		memcpy(uncommon_weight_pol[i], common_term_weight_pol, sizeof(long long) * d_y_num);
  		memcpy(uncommon_weight_pol_1_k_1[i], common_term_weight_pol_1_k_1, sizeof(long long) * d_y_num);
  		memcpy(uncommon_lexorder_pol[i], common_term_lexorder_pol, sizeof(long long) * d_y_num);
  	}
#if (1 == CFG_DEBUG_NOTICE)  	
  	for(i = 0; i < pow_val; i++)
  	{
  		for(j = 0; j < d_y_num; j++)
  		{
  			DEBUG_NOTICE("uncommon_weight: %ld %ld %ld %ld %ld\n",
  			             i,
  			             j,
  			             uncommon_weight_pol[i][j],
  			             uncommon_weight_pol_1_k_1[i][j],
  			             uncommon_lexorder_pol[i][j]);
  		}
  	}
#endif  	
	
	uncommon_l_s = (long long*)malloc(sizeof(long long) * pow_val);
	uncommon_l_o = (long long*)malloc(sizeof(long long) * pow_val);
	uncommon_l_w = (long long*)malloc(sizeof(long long) * pow_val);
	for(i = 0; i < pow_val; i++)
	{
		uncommon_l_s[i] = common_l_s;
		uncommon_l_w[i] = common_l_w;
		uncommon_l_o[i] = common_l_o;
	}
#endif

	uncommon_term_c_choose = (unsigned char**)malloc(sizeof(unsigned char*) * pow_val);
	for(i = 0; i < pow_val; i++)
	{
		uncommon_term_c_choose[i] = (unsigned char*)malloc(sizeof(unsigned char) * term_size_p);
  	}
  	for(i = 0; i < pow_val; i++)
	{
		memset(uncommon_term_c_choose[i], 0xFF, sizeof(unsigned char) * term_size_p);
  	}
  	
  	unsigned char unrel_place_flag = 0;
  	long long unrel_place_idx = 0;
  	uncommon_decoded_codeword = (unsigned char**)malloc(sizeof(unsigned char*) * pow_val);
  	uncommon_decoded_message = (unsigned char**)malloc(sizeof(unsigned char*) * pow_val);
  	
#if (1 == CFG_BR)
  	tst_vct_cmm = (unsigned char*)malloc(sizeof(unsigned char) * CODEWORD_LEN);
  	for(j = 0; j < CODEWORD_LEN; j++)
  	{
  		unrel_place_flag = 0;
		for(k = 0; k < YITA; k++)
		{
			if(j == uncommon_place[k])
			{
				unrel_place_flag = 1;
				unrel_place_idx = k;
				break;
			}
		}
		
		if(1 == unrel_place_flag)
		{
			//tst_vct_cmm[j] = power_polynomial_table[uncommon_seq[unrel_place_idx][i]][0];
			tst_vct_cmm[j] = 0xFF;
		}
		else
		{
			tst_vct_cmm[j] = received_polynomial[j];
		}

		if(0xFF != tst_vct_cmm[j])
		{
  			DEBUG_NOTICE("tst_vct_cmm: %ld | %x %x | %x %x\n", j, tst_vct_cmm[j], encoded_polynomial[j], intrplt_seq[j], beta_matrix[tst_vct_cmm[j] + 1][intrplt_seq[j]]);
		}
		else
		{
			DEBUG_NOTICE("tst_vct_cmm: %ld | %x %x | %x %x\n", j, tst_vct_cmm[j], encoded_polynomial[j], intrplt_seq[j], beta_matrix[0][intrplt_seq[j]]);
		}
  	}
#endif
  	
  	tst_vct = (unsigned char**)malloc(sizeof(unsigned char*) * pow_val);
	for(i = 0; i < pow_val; i++)
	{
		uncommon_decoded_codeword[i] = (unsigned char*)malloc(sizeof(unsigned char) * CODEWORD_LEN);
		uncommon_decoded_message[i] = (unsigned char*)malloc(sizeof(unsigned char) * MESSAGE_LEN);
		tst_vct[i] = (unsigned char*)malloc(sizeof(unsigned char) * CODEWORD_LEN);
  	}
  	long long best_tv_idx = 0;
  	for(i = 0; i < pow_val; i++)
	{
		memset(uncommon_decoded_codeword[i], 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
		memset(uncommon_decoded_message[i], 0xFF, sizeof(unsigned char) * MESSAGE_LEN);
		
		for(j = 0; j < CODEWORD_LEN; j++)
		{
			unrel_place_flag = 0;
			for(k = 0; k < YITA; k++)
			{
				if(j == uncommon_place[k])
				{
					unrel_place_flag = 1;
					unrel_place_idx = k;
					break;
				}
			}
			
			if(1 == unrel_place_flag)
			{
				tst_vct[i][j] = power_polynomial_table[uncommon_seq[unrel_place_idx][i]][0];
			}
			else
			{
				tst_vct[i][j] = received_polynomial[j];
			}
			DEBUG_NOTICE("tst_vct: %ld %ld | %x %x | %x %x\n", i, j, tst_vct[i][j], encoded_polynomial[j], intrplt_seq[j], beta_matrix[tst_vct[i][j] + 1][intrplt_seq[j]]);
			
			if((0 == i)
				&& (tst_vct[i][j] != received_polynomial[j]))
			{
				DEBUG_SYS("tst_err: %ld | %d %d %d | %d %d %d | %d %d | %f %f %f\n",
						  j,
						  tst_vct[i][j],
						  received_polynomial[j],
						  encoded_polynomial[j],
						  unrel_place_idx,
						  uncommon_seq[unrel_place_idx][i],
						  uncommon_place[unrel_place_idx],
						  chnl_rel_max_id[uncommon_place[unrel_place_idx]],
						  chnl_rel_scd_id[uncommon_place[unrel_place_idx]],
						  chnl_rel_matrix[chnl_rel_max_id[uncommon_place[unrel_place_idx]]][j],
						  chnl_rel_matrix[chnl_rel_scd_id[uncommon_place[unrel_place_idx]]][j],
						  chnl_rel_matrix[received_polynomial[j] + 1][j]);
			}
		}
		
		/*for debug*/
		long long tmp_cnt = 0;
		for(j = 0; j < CODEWORD_LEN; j++)
		{
			if(tst_vct[i][j] != encoded_polynomial[j])
			{
				tmp_cnt++;
			}
		}
		DEBUG_IMPOTANT("tst_vct_diff: %ld | %ld\n", i, tmp_cnt);
		if(best_tst_vct_diff > tmp_cnt)
		{
			best_tst_vct_diff = tmp_cnt;
			best_tv_idx = i;
		}
		tmp_cnt = 0;
  	}
  	memcpy(tst_vct_debug, tst_vct[best_tv_idx], sizeof(unsigned char) * CODEWORD_LEN);

#if 1/*rarely happen*/
	for(i = 0; i < MESSAGE_LEN; i++)
	{
		if(encoded_polynomial[rel_group_seq[i]] != received_polynomial[rel_group_seq[i]])
		{
			break;
		}
	}
	if((MESSAGE_LEN == i)
		&& (((CODEWORD_LEN - MESSAGE_LEN) / 2) < best_tst_vct_diff))
	{
		DEBUG_IMPOTANT("erasure decoding enhance: %ld\n", best_tst_vct_diff);
	}
#endif

#if (1 == CFG_ADAPTIVE_PARALLEL)
	tst_vct_seq = (long long**)malloc(sizeof(long long*) * pow_val);
	for(i = 0; i < pow_val; i++)
	{
		tst_vct_seq[i] = (long long*)malloc(sizeof(long long) * pow_val);
	}
#else
	tst_vct_seq = (long long**)malloc(sizeof(long long*) * PARALLEL_BATCH_NUM);
	for(i = 0; i < PARALLEL_BATCH_NUM; i++)
	{
		tst_vct_seq[i] = (long long*)malloc(sizeof(long long) * (pow_val / PARALLEL_BATCH_NUM));
	}
#endif	
	decoded_tst_vct_seq = (long long*)malloc(sizeof(long long) * pow_val);
	memset(decoded_tst_vct_seq, 0, sizeof(long long) * pow_val);
	
#if (1 == CFG_STORE_PARALEL)
	long long sort_len = (long long)pow(2, CFG_STORE_LEN);
	long long store_size = pow_val / sort_len;
	store_uncommon_table_c_prev = (unsigned char***)malloc(sizeof(unsigned char**) * store_size);
	for (i = 0; i < store_size; i++)
	{
  		store_uncommon_table_c_prev[i] = (unsigned char**)malloc(sizeof(unsigned char*) * d_y_num);

		for(j = 0; j < d_y_num; j++)
		{
			store_uncommon_table_c_prev[i][j] = (unsigned char*)malloc(sizeof(unsigned char) * term_size_p);
		}
  	}

  	store_flag = (unsigned char*)malloc(sizeof(unsigned char) * store_size);
  	memset(store_flag, 0, sizeof(unsigned char) * store_size);

  	store_group = (long long**)malloc(sizeof(long long*) * store_size);
	for(i = 0; i < store_size; i++)
	{
		store_group[i] = (long long*)malloc(sizeof(long long) * sort_len);
	}
#endif

	chnl_rel_thrd_cnt = 0;
	tst_vct_rel = (float*)malloc(sizeof(float) * pow_val);
	for(i = 0; i < pow_val; i++)
	{
		tst_vct_rel[i] = 1;
		for(j = 0; j < YITA; j++)
		{
#if 0		
			DEBUG_NOTICE("tst_vct_rel: %d %d | %f | %f\n",
		                 uncommon_place[j],
		             	 uncommon_seq[j][i],
		             	 chnl_rel_matrix[uncommon_seq[j][i]][uncommon_place[j]],
		             	 tst_vct_rel[i]);
#endif		             	 
			tst_vct_rel[i] = tst_vct_rel[i] * chnl_rel_matrix[uncommon_seq[j][i]][uncommon_place[j]];
		}
		DEBUG_NOTICE("tst_vct_rel: %d | %f\n",
		              i,
		              tst_vct_rel[i]);
		             
		if((0 != i)
			&& (CFG_CHNL_REL_THRD <= (tst_vct_rel[i] * 100 / tst_vct_rel[0])))
		{
			chnl_rel_thrd_cnt++;
		}
	}
	DEBUG_NOTICE("chnl_rel_thrd_cnt: %ld\n", chnl_rel_thrd_cnt);

#if (1 == CFG_IMD_STORE)
	store_q_c_prev = (unsigned char****)malloc(sizeof(unsigned char***) * YITA);
	store_q_c_flag = (unsigned char**)malloc(sizeof(unsigned char*) * YITA);
	for (i = 0; i < YITA; i++)
	{
  		store_q_c_prev[i] = (unsigned char***)malloc(sizeof(unsigned char**) * pow_val);
		store_q_c_flag[i] = (unsigned char*)malloc(sizeof(unsigned char) * pow_val);
		memset(store_q_c_flag[i], 0, sizeof(unsigned char) * pow_val);

		for(j = 0; j < pow_val; j++)
		{
			store_q_c_prev[i][j] = (unsigned char**)malloc(sizeof(unsigned char*) * d_y_num);
			
			for(k = 0; k < d_y_num; k++)
			{
				store_q_c_prev[i][j][k] = (unsigned char*)malloc(sizeof(unsigned char) * term_size_p);
			}
		}
  	}
#endif  	

	adaptive_vct_seq = (long long*)malloc(sizeof(long long) * pow_val);
	adaptive_vct_seq_mark = (unsigned char*)malloc(sizeof(unsigned char) * pow_val);
	memset(adaptive_vct_seq_mark, 0, sizeof(unsigned char) * pow_val);

	return 0;
}

int uncommon_interpolation(long long l)
{
	long long i = 0, j = 0, k = 0;
	//long long l = 0;
	long long m = 0, n = 0, term_num = 0, term_num_real = term_size_p;
	long long d_x = term_size_x + 1;
	long long d_y = term_size_y + 1;
	long long tmp_sum = 0;
	unsigned char tmp_ff = 0xFF;
	//long long l_s = 0x7FFF, l_o = 0x7FFF, l_w = 0;
	long long tmp_real = 0;
	long long tmp_mul = S_MUL;
	
	unsigned char locator_seq[CODEWORD_LEN];
	for(i = 0; i < CODEWORD_LEN; i++)
	{
		locator_seq[i] = power_polynomial_table[i + 1][0];
	}
	
	long long *term_use_index;

	long long *g_table_x;
	long long *g_table_y;
#if (0 == TERM_SIZE_DBG)
	g_table_x = (long long*)malloc(sizeof(long long) * term_num_real);
	g_table_y = (long long*)malloc(sizeof(long long) * term_num_real);
	memset(g_table_x, 0, sizeof(long long) * term_num_real);
	memset(g_table_y, 0, sizeof(long long) * term_num_real);
	k = 0;
	for(i = 0; i < (d_x + 0); i++)
	{
		for(j = 0; j < (d_y + 0); j++)
		{
			//if(S_MUL > (i + j))
			{
				g_table_x[k] = i;
				g_table_y[k] = j;
				DEBUG_NOTICE("g_table: %d %d %d\n", k, g_table_x[k], g_table_y[k]);
				k = k + 1;
			}
		}
	}
#else
	g_table_x = (long long*)malloc(sizeof(long long) * (term_size_x * term_size_y));
	g_table_y = (long long*)malloc(sizeof(long long) * (term_size_x * term_size_y));
	memcpy(g_table_x, g_term_x, sizeof(long long) * (term_size_x * term_size_y));
	memcpy(g_table_y, g_term_y, sizeof(long long) * (term_size_x * term_size_y));
#endif

	unsigned char *discrepancy;
	discrepancy = (unsigned char*)malloc(sizeof(unsigned char) * d_y_num);
	memset(discrepancy, 0xFF, sizeof(unsigned char) * d_y_num);

	unsigned char *tmp_table_c;
	tmp_table_c = (unsigned char*)malloc(sizeof(unsigned char) * term_num_real);
	memset(tmp_table_c, 0xFF, sizeof(unsigned char) * term_num_real);

	long long lex_order_table[d_x][d_y];
#if (1 == RE_ENCODING)
	lex_order((long long **)lex_order_table, d_x, d_y, Y_WEIGHT);
#else
	lex_order((long long **)lex_order_table, d_x, d_y, (MESSAGE_LEN - 1));
#endif

#if (1 == CFG_STORE_PARALEL)
	long long sort_len = (long long)pow(2, CFG_STORE_LEN);
	long long store_size = pow_val / sort_len;

	//long long store_batch_idx = l / (pow_val / PARALLEL_BATCH_NUM);
	//long long store_flag = l % (pow_val / PARALLEL_BATCH_NUM);
	long long store_batch_idx = -1, store_in_idx = -1;
	for(i = 0; i < store_size; i++)
	{
		for(j = 0; j < sort_len; j++)
		{
			if(l == store_group[i][j])
			{
				store_batch_idx = i;
				store_in_idx = j;
				break;
			}
		}

		if(-1 != store_in_idx)
		{
			break;
		}
	}
	//long long store_flag = l % (pow_val / store_size);
	if((-1 == store_batch_idx)
		|| (-1 == store_in_idx))
	{
		DEBUG_SYS("store_err: %ld %ld\n", store_batch_idx, store_in_idx);
	}

	if(-1 == store_place)
	{
		//store_place = CODEWORD_LEN - ((long long)log2(pow_val / PARALLEL_BATCH_NUM)) - 1;
		store_place = CODEWORD_LEN - 1 - CFG_STORE_LEN;
		DEBUG_INFO("store_place: %ld\n", store_place);
	}
#endif

	/*interpolation*/
	//for(l = 0; l < pow_val; l++)
	{

		for(j = (CODEWORD_LEN - YITA); j < CODEWORD_LEN; j++) //for I, as 2^q - 1
		{
#if (1 == CFG_STORE_PARALEL)		
			if((store_place >= j)
			   && (1 == store_flag[store_batch_idx]))
			{
				DEBUG_INFO("l_j: %ld %ld\n", l, j);
				if(store_place == j)
				{
					store_q_poly_load(store_batch_idx, l);
				}
				continue;
			}
			
			store_cnt++;
#endif

#if (1 == CFG_IMD_STORE)
			if(1 == store_q_c_flag[j - (CODEWORD_LEN - YITA)][l])
			{
				continue;
			}
			intp_cnt++;

			long long layer_load = j - (CODEWORD_LEN - YITA);
			long long node_load = l;
			if(0 == store_q_c_flag[j - (CODEWORD_LEN - YITA)][l])
			{
				for(layer_load = j - (CODEWORD_LEN - YITA); layer_load >= 0; layer_load--)
				{
					DEBUG_INFO("node_load: %ld %ld | %d\n",
					           layer_load,
					           node_load,
					           store_q_c_flag[layer_load][node_load]);
					if(1 == store_q_c_flag[layer_load][node_load])
					{
						store_q_c_load(layer_load, node_load, l);
						DEBUG_IMPOTANT("load_q_c: %ld %ld %ld\n",
									   layer_load,
									   node_load,
									   l);
						break;			   
					}
				}
				
				for(m = 0; m < d_y_num; m++)
				{
					for(n = 0; n < term_num_real; n++)
					{
						if(0xFF != uncommon_table_c_prev[l][m][n])
						{
							DEBUG_NOTICE("g_table_c_prev: %d | %d | %d %d | %d %d | %d %d | %d\n",
								          l,
								          m,
								          lex_order_table[g_table_x[n]][g_table_y[n]],
								          (g_table_x[n] + (MESSAGE_LEN - 1) * g_table_y[n]),
								          g_table_x[n],
								          g_table_y[n],
								          g_term_x[n],
								          g_term_y[n],
								          uncommon_table_c_prev[l][m][n]);
						}
					}
				}
			}
#if 1
			for(m = 0; m < d_y_num; m++)
			{
				uncommon_weight_pol[l][m] = -100;
				uncommon_lexorder_pol[l][m] = 0x7FFF;

				uncommon_weight_pol_1_k_1[l][m] = 0;
				
				for(n = 0; n < term_num_real; n++)
				{
					if(0xFF != uncommon_term_c_p[l][m][n])
					{
						if((uncommon_weight_pol[l][m] < (g_table_x[n] + Y_WEIGHT * g_table_y[n]))
							|| ((uncommon_weight_pol[l][m] == (g_table_x[n] + Y_WEIGHT * g_table_y[n])) 
								&& (uncommon_lexorder_pol[l][m] > lex_order_table[g_table_x[n]][g_table_y[n]])))
						{
							uncommon_weight_pol[l][m] = (g_table_x[n] + Y_WEIGHT * g_table_y[n]);
							uncommon_lexorder_pol[l][m] = lex_order_table[g_table_x[n]][g_table_y[n]];
							if((g_table_x[n] >= d_x)
								|| (g_table_y[n] >= d_y))
							{
								DEBUG_IMPOTANT("lex_order_table_err: %ld | %ld %ld | %ld %ld | %ld\n",
											   n,
									           g_table_x[n],
									           g_table_y[n],
									           d_x,
									           d_y,
									           uncommon_lexorder_pol[l][m]);
							}
							DEBUG_NOTICE("pol_updating: %d %d\n", uncommon_weight_pol[l][m], uncommon_lexorder_pol[l][m]);
						}

						if((uncommon_weight_pol_1_k_1[l][m] < (g_table_x[n] + (MESSAGE_LEN - 1) * g_table_y[n]))
							|| ((uncommon_weight_pol_1_k_1[l][m] == (g_table_x[n] + (MESSAGE_LEN - 1) * g_table_y[n])) 
								&& (uncommon_lexorder_pol[l][m] > lex_order_table[g_table_x[n]][g_table_y[n]])))
						{
							uncommon_weight_pol_1_k_1[l][m] = (g_table_x[n] + (MESSAGE_LEN - 1) * g_table_y[n]);
							uncommon_lexorder_pol[l][m] = lex_order_table[g_table_x[n]][g_table_y[n]];
							if((g_table_x[n] >= d_x)
								|| (g_table_y[n] >= d_y))
							{
								DEBUG_IMPOTANT("lex_order_table_err: %ld | %ld %ld | %ld %ld | %ld\n",
											   n,
									           g_table_x[n],
									           g_table_y[n],
									           d_x,
									           d_y,
									           uncommon_lexorder_pol[l][m]);
							}
							DEBUG_NOTICE("pol_updating_1-k-1: %d | %d %d\n", l, uncommon_weight_pol_1_k_1[l][m], uncommon_lexorder_pol[l][m]);
						}
					}
				}
				DEBUG_NOTICE("pol: %d | %d %d %d %d\n", l, m, uncommon_weight_pol[l][m], uncommon_lexorder_pol[l][m], uncommon_weight_pol_1_k_1[l][m]);
			}
			uncommon_l_w[l] = uncommon_weight_pol[l][uncommon_l_s[l]];//uncommon_weight_pol[l][uncommon_l_s[l]];
			uncommon_l_o[l] = uncommon_lexorder_pol[l][uncommon_l_s[l]];
#endif
#else
			intp_cnt++;
#endif
		
#if (1 == BF_INTERPOLATION)
			if((1 == (l % 2))
				&& ((CODEWORD_LEN - 2) >= j))
			{
				continue;
			}
#endif
		
			for(i = 0; i < (CODEWORD_LEN + 1); i++)//for I, as n
			{
#if 0				
				if(0 == mul_matrix[i][intrplt_seq[j]])
				{
					continue;
				}
#else
				if(i != uncommon_seq[j - (CODEWORD_LEN - YITA)][l])
				{
					/*the test vector is chosen here!!!*/
					continue;
				}
#endif
				DEBUG_INFO("-------------------------------------------\n");
				DEBUG_INFO("point: %d | %d %d | %d %d | (%x %x)\n", l, CODEWORD_LEN, (CODEWORD_LEN + 1), i, intrplt_seq[j], locator_seq[intrplt_seq[j]], beta_matrix[i][intrplt_seq[j]]);

				/*the (a, b) pairs should be init here*/
				term_num = 0;//clear here
				for(m = 0; m < d_x; m++)
				{
					for(n = 0; n < d_y; n++)
					{
						if((tmp_mul - 1) >= (m + n))
						{
							term_num = term_num + 1;
						}
					}
				}

				DEBUG_NOTICE("term_num: %d\n", term_num);

				term_use_index = (long long*)malloc(sizeof(long long) * term_num);
				m = 0;
				for(k = 0; k < term_num_real; k++)
				{
					if((tmp_mul - 1) >= (g_table_x[k] + g_table_y[k]))
					{
						term_use_index[m] = k;
						DEBUG_NOTICE("term_use_index: %d | %d | %d %d\n", m, term_use_index[m], g_table_x[k], g_table_y[k]);
						m = m + 1;
					}
				}

				/*notice that only (a, b) pairs is constained by (a + b) < m directly.*/
				/*(r, s) pairs is related to the point (a, b), but not the constrain.*/
				for(k = 0; k < term_num; k++) //for II, as (a, b) pairs
				{
					DEBUG_NOTICE("*********************\n");
					DEBUG_NOTICE("k ready: %d %d | %d | (%d %d)\n", term_num, k, term_use_index[k], g_table_x[term_use_index[k]], g_table_y[term_use_index[k]]);
					memset(discrepancy, 0xFF, sizeof(unsigned char) * d_y_num);

					for(m = 0; m < d_y_num; m++) //for III, as Q_d_y_max
					{
						/*this itertation is used to calculate discrepancy and record l_s place*/
						tmp_sum = 0xFF;

						for(n = 0; n < term_num_real; n++) //for IV, as (r, s) pairs
						{
#if 0
							DEBUG_NOTICE("n_iter: %ld %ld | %ld %ld | %x | %x | %d %d\n",
							             g_table_x[n],
							             g_table_x[term_use_index[k]],
							             g_table_y[n],
							             g_table_y[term_use_index[k]],
							             uncommon_table_c_prev[l][m][n],
							             beta_matrix[i][intrplt_seq[j]],
							             g_table_y[n],
							             g_table_y[term_use_index[k]]);
#endif							             
							if((g_table_x[n] < g_table_x[term_use_index[k]])
								|| (g_table_y[n] < g_table_y[term_use_index[k]])
								|| (0xFF == uncommon_table_c_prev[l][m][n])
								|| ((0xFF == beta_matrix[i][intrplt_seq[j]]) && (g_table_y[n] != g_table_y[term_use_index[k]])))
							{
								continue;
							}

							DEBUG_NOTICE("++++++++++\n");
							DEBUG_NOTICE("(m, n) ready: %d (%d %d) %x\n", m, g_table_x[n], g_table_y[n], uncommon_table_c_prev[l][m][n]);
							tmp_real = real_combine(g_table_x[n], g_table_x[term_use_index[k]]) * real_combine(g_table_y[n], g_table_y[term_use_index[k]]);
							//DEBUG_NOTICE("tmp_real: %d | %d %d %d | %d %d %d\n", tmp_real, g_table_x[n], g_table_x[term_use_index[k]], real_combine(g_table_x[n], g_table_x[term_use_index[k]]), g_table_y[n], g_table_y[term_use_index[k]], real_combine(g_table_y[n], g_table_y[term_use_index[k]]));
							tmp_ff = gf_real_mutp_ff(tmp_real, uncommon_table_c_prev[l][m][n]);
							//DEBUG_NOTICE("tmp_ff: %x = %d mul %x\n", tmp_ff, tmp_real, g_table_c_prev[m][n]);
							//DEBUG_NOTICE("tmp_ff: %x * (%x = %x^%x)\n", tmp_ff, gf_pow_cal(power_polynomial_table[j + 1][0], (g_table_x[n] - g_table_x[term_use_index[k]])), power_polynomial_table[j + 1][0], (g_table_x[n] - g_table_x[term_use_index[k]]));
							tmp_ff = gf_multp(tmp_ff, gf_pow_cal(locator_seq[intrplt_seq[j]], (g_table_x[n] - g_table_x[term_use_index[k]])));
							//DEBUG_NOTICE("tmp_ff: %x * (%x = %x^%x)\n", tmp_ff, gf_pow_cal(beta_matrix[i][j], (g_table_y[n] - g_table_y[term_use_index[k]])), beta_matrix[i][j], (g_table_y[n] - g_table_y[term_use_index[k]]));
							tmp_ff = gf_multp(tmp_ff, gf_pow_cal(beta_matrix[i][intrplt_seq[j]], (g_table_y[n] - g_table_y[term_use_index[k]])));
							//DEBUG_NOTICE("gf_add: %x + %x\n", tmp_sum, tmp_ff);
							tmp_sum = gf_add(tmp_sum, tmp_ff);
#if (1 == CFG_DEBUG_NOTICE)						
							if(0xFF != tmp_sum)
							{
								DEBUG_NOTICE("tmp_sum: %d | %d\n", tmp_sum, tmp_ff);
							}
#endif						
						}
						
						if(0xFF != tmp_sum)
						{
							discrepancy[m] = tmp_sum;
							DEBUG_NOTICE("d: %d | %d %d | %d %d | %d | %d\n", l, i, j, g_table_x[term_use_index[k]], g_table_y[term_use_index[k]], m, discrepancy[m]);
						}

						if(0xFF != discrepancy[m])
						{
							DEBUG_NOTICE("updating place center: %d | %d vs %d | %d vs %d\n", uncommon_l_s[l], uncommon_l_w[l], uncommon_weight_pol[l][m], uncommon_l_o[l], uncommon_lexorder_pol[l][m]);
							if(((uncommon_l_w[l] > uncommon_weight_pol[l][m])
									|| ((uncommon_l_w[l] == uncommon_weight_pol[l][m])
										&& (uncommon_l_o[l] > uncommon_lexorder_pol[l][m])))
								|| (0xFF == discrepancy[uncommon_l_s[l]]))
							{
								uncommon_l_s[l] = m;
								uncommon_l_w[l] = uncommon_weight_pol[l][m];
								uncommon_l_o[l] = uncommon_lexorder_pol[l][m];
								DEBUG_NOTICE("updated place center: %d | %d | %d\n", uncommon_l_s[l], uncommon_l_w[l], uncommon_l_o[l]);
							}
						}
					}

					DEBUG_NOTICE("l_s: %d | %d\n", l, uncommon_l_s[l]);
#if 1
					for(m = 0; m < d_y_num; m++)//update normal Q_l
					{
						if((m == uncommon_l_s[l])
							|| (0xFF == discrepancy[m]))
						{
							continue;
						}
						
						for(n = 0; n < term_num_real; n++)
						{
							//g_table_c[m][n] = gf_multp(g_table_c_prev[m][n], discrepancy[l_s]);
							uncommon_term_c_p[l][m][n] = gf_multp(uncommon_table_c_prev[l][m][n], 0x0);
						}
						
						for(n = 0; n < term_num_real; n++)
						{
							tmp_table_c[n] = gf_multp(uncommon_table_c_prev[l][uncommon_l_s[l]][n], discrepancy[m]);
							tmp_table_c[n] = gf_div(tmp_table_c[n], discrepancy[uncommon_l_s[l]]);
						}

						for(n = 0; n < term_num_real; n++)
						{
							uncommon_term_c_p[l][m][n] = gf_add(uncommon_term_c_p[l][m][n], tmp_table_c[n]);
						}
#if (1 == CFG_DEBUG_NOTICE)
						for(n = 0; n < term_num_real; n++)
						{
							if(0xFF != uncommon_term_c_p[l][m][n])
							{
								DEBUG_NOTICE("Q_l: %d | %d | %d %d | %x\n", l, m, g_table_x[n], g_table_y[n], uncommon_term_c_p[l][m][n]);
							}
						}
#endif					
					}

					memset(tmp_table_c, 0xFF, sizeof(unsigned char) * term_num_real);
					for(n = 0; n < term_num_real; n++)//update Q_l_s
					{
						if(0xFF == discrepancy[uncommon_l_s[l]])
						{
							DEBUG_NOTICE("no update for this (a, b) pair: %d\n", uncommon_l_s[l]);
							break;
						}
						
						if(0xFF != uncommon_table_c_prev[l][uncommon_l_s[l]][n])
						{
							//DEBUG_NOTICE("update Q_l_s: %d %d | %d %d | %x\n", l_s, n, g_table_x[n], g_table_y[n], g_table_c[l_s][n]);
							for(m = 0; m < term_num_real; m++)
							{
								//DEBUG_NOTICE("checking m: %d | %d %d | %x\n", m, g_table_x[m], g_table_y[m], g_table_c[l_s][m]);
								if((g_table_x[m] == (g_table_x[n] + 1))
									&& (g_table_y[m] == g_table_y[n]))
								{
									tmp_table_c[m] = gf_add(uncommon_table_c_prev[l][uncommon_l_s[l]][n], tmp_table_c[m]);
									//DEBUG_NOTICE("update tmp_table_c[m]: %d %d | %d %d | %x\n", m, n, g_table_x[m], g_table_y[m], tmp_table_c[m]);
									break;
								}
							}

							tmp_table_c[n] = gf_add(gf_multp(uncommon_table_c_prev[l][uncommon_l_s[l]][n], locator_seq[intrplt_seq[j]]), tmp_table_c[n]);
						}
					}
					for(n = 0; n < term_num_real; n++)
					{
						if(0xFF == discrepancy[uncommon_l_s[l]])
						{
							DEBUG_NOTICE("no update for this (a, b) pair: %d\n", uncommon_l_s[l]);
							break;
						}

						uncommon_term_c_p[l][uncommon_l_s[l]][n] = 0xFF;

						if(0xFF != tmp_table_c[n])
						{
							//g_table_c[l_s][n] = gf_multp(tmp_table_c[n], discrepancy[l_s]);
							//uncommon_term_c_p[l][uncommon_l_s[l]][n] = gf_multp(tmp_table_c[n], 0x0);
							uncommon_term_c_p[l][uncommon_l_s[l]][n] = tmp_table_c[n];
							DEBUG_NOTICE("Q_l_s_c: %d | %d | %d %d | %x\n", l, uncommon_l_s[l], g_table_x[n], g_table_y[n], uncommon_term_c_p[l][uncommon_l_s[l]][n]);
						}
					}
#endif
#if 1
					for(m = 0; m < d_y_num; m++)
					{
						uncommon_weight_pol[l][m] = -100;
						uncommon_lexorder_pol[l][m] = 0x7FFF;

						uncommon_weight_pol_1_k_1[l][m] = 0;
						
						for(n = 0; n < term_num_real; n++)
						{
							if(0xFF != uncommon_term_c_p[l][m][n])
							{
								if((uncommon_weight_pol[l][m] < (g_table_x[n] + Y_WEIGHT * g_table_y[n]))
									|| ((uncommon_weight_pol[l][m] == (g_table_x[n] + Y_WEIGHT * g_table_y[n])) 
										&& (uncommon_lexorder_pol[l][m] > lex_order_table[g_table_x[n]][g_table_y[n]])))
								{
									uncommon_weight_pol[l][m] = (g_table_x[n] + Y_WEIGHT * g_table_y[n]);
									uncommon_lexorder_pol[l][m] = lex_order_table[g_table_x[n]][g_table_y[n]];
									if((g_table_x[n] >= d_x)
										|| (g_table_y[n] >= d_y))
									{
										DEBUG_IMPOTANT("lex_order_table_err: %ld | %ld %ld | %ld %ld | %ld\n",
													   n,
											           g_table_x[n],
											           g_table_y[n],
											           d_x,
											           d_y,
											           uncommon_lexorder_pol[l][m]);
									}
									DEBUG_NOTICE("pol_updating: %d %d\n", uncommon_weight_pol[l][m], uncommon_lexorder_pol[l][m]);
								}

								if((uncommon_weight_pol_1_k_1[l][m] < (g_table_x[n] + (MESSAGE_LEN - 1) * g_table_y[n]))
									|| ((uncommon_weight_pol_1_k_1[l][m] == (g_table_x[n] + (MESSAGE_LEN - 1) * g_table_y[n])) 
										&& (uncommon_lexorder_pol[l][m] > lex_order_table[g_table_x[n]][g_table_y[n]])))
								{
									uncommon_weight_pol_1_k_1[l][m] = (g_table_x[n] + (MESSAGE_LEN - 1) * g_table_y[n]);
									uncommon_lexorder_pol[l][m] = lex_order_table[g_table_x[n]][g_table_y[n]];
									if((g_table_x[n] >= d_x)
										|| (g_table_y[n] >= d_y))
									{
										DEBUG_IMPOTANT("lex_order_table_err: %ld | %ld %ld | %ld %ld | %ld\n",
													   n,
											           g_table_x[n],
											           g_table_y[n],
											           d_x,
											           d_y,
											           uncommon_lexorder_pol[l][m]);
									}
									DEBUG_NOTICE("pol_updating_1-k-1: %d | %d %d\n", l, uncommon_weight_pol_1_k_1[l][m], uncommon_lexorder_pol[l][m]);
								}
							}
						}
						DEBUG_NOTICE("pol: %d | %d %d %d %d\n", l, m, uncommon_weight_pol[l][m], uncommon_lexorder_pol[l][m], uncommon_weight_pol_1_k_1[l][m]);
					}
					uncommon_l_w[l] = uncommon_weight_pol[l][uncommon_l_s[l]];//uncommon_weight_pol[l][uncommon_l_s[l]];
					uncommon_l_o[l] = uncommon_lexorder_pol[l][uncommon_l_s[l]];
#endif
					/*store g as prev_poly*/
					for(m = 0; m < d_y_num; m++)
					{
						for(n = 0; n < term_num_real; n++)
						{
							uncommon_table_c_prev[l][m][n] = uncommon_term_c_p[l][m][n];
#if (1 == CFG_DEBUG_NOTICE)						
							if(0xFF != uncommon_table_c_prev[l][m][n])
							{
								DEBUG_NOTICE("g_table_c_prev: %d | %d | %d %d | %d %d | %d %d | %d\n",
									          l,
									          m,
									          lex_order_table[g_table_x[n]][g_table_y[n]],
									          (g_table_x[n] + (MESSAGE_LEN - 1) * g_table_y[n]),
									          g_table_x[n],
									          g_table_y[n],
									          g_term_x[n],
									          g_term_y[n],
									          uncommon_table_c_prev[l][m][n]);
							}
#endif

							if(0xFF != uncommon_table_c_prev[l][m][n])
							{
								if(g_table_x[n] > max_dx)
								{
									max_dx = g_table_x[n];
									//DEBUG_SYS("max_dx: %ld\n", max_dx);
								}
								if(g_table_y[n] > max_dy)
								{
									max_dy = g_table_y[n];
									//DEBUG_SYS("max_dy: %ld\n", max_dy);
								}
							}
						}
					}
				}

				free(term_use_index);
				term_use_index = NULL;
			}
#if (1 == CFG_STORE_PARALEL)			
			if((store_place == j)
			   && (0 == store_flag[store_batch_idx]))
			{
				store_q_poly_save(store_batch_idx, l);
				store_flag[store_batch_idx] = 1;
			}
#endif

#if (1 == CFG_IMD_STORE)
			store_q_c_save(j - (CODEWORD_LEN - YITA), l, l);
#endif

#if (1 == BF_INTERPOLATION)
			if((0 == (l % 2))
				&& ((CODEWORD_LEN - 1) == j))
			{
				bf_polynomial_process(locator_seq[intrplt_seq[j]],
				                      uncommon_table_c_prev[l],
				                      uncommon_table_c_prev[l + 1]);
			}
#endif			
		}
	
	}

	//for(l = 0; l < pow_val; l++)
	{
		DEBUG_NOTICE("---------------\n");
		for(m = 0; m < d_y_num; m++)
		{
			for(n = 0; n < term_num_real; n++)
			{
#if (1 == CFG_DEBUG_NOTICE)						
				if(0xFF != uncommon_table_c_prev[l][m][n])
				{
					DEBUG_NOTICE("g_table_c_lcc: %d | %d | %d %d | %d %d | %d\n",
						          l,
						          m,
						          lex_order_table[g_table_x[n]][g_table_y[n]],
						          (g_table_x[n] + (MESSAGE_LEN - 1) * g_table_y[n]),
						          g_table_x[n],
						          g_table_y[n],
						          uncommon_table_c_prev[l][m][n]);
				}
#endif
			}
		}
	}

	//for(l = 0; l < pow_val; l++)
	{
		/*find the place of smallest polynomial*/
		tmp_real = 0x7FFF;//notice this, it should be init large enough
		for(m = 0; m < d_y_num; m++)
		{
			if(tmp_real > uncommon_weight_pol[l][m])
			{
				DEBUG_NOTICE("sml_updated: %d | %d %d | %d\n", m, tmp_real, uncommon_weight_pol[l][m], uncommon_lexorder_pol[l][m]);
				sml_poly = m;
				tmp_real = uncommon_weight_pol[l][m];
			}
			if((tmp_real == uncommon_weight_pol[l][m])
				&& (uncommon_lexorder_pol[l][sml_poly] > uncommon_lexorder_pol[l][m]))
			{
				DEBUG_NOTICE("sml_updated: %d | %d %d | %d\n", m, tmp_real, uncommon_weight_pol[l][m], uncommon_lexorder_pol[l][m]);
				sml_poly = m;
			}
		}

		/*copy the interpolated polynomials to global memory*/
		for(n = 0; n < term_num_real; n++)
		{
			if(0xFF != uncommon_table_c_prev[l][sml_poly][n])
			{
				for(k = 0; k < (term_size_x * term_size_y); k++)
				{
					if((g_table_x[n] == g_term_x[k])
						&& (g_table_y[n] == g_term_y[k]))
					{
						uncommon_term_c_choose[l][k] = uncommon_table_c_prev[l][sml_poly][n];
						DEBUG_IMPOTANT("uncommon_g_term: %d | %d %d | %d %d | %x\n", 
									   l,
									   k,
									   sml_poly,
									   g_term_x[k],
									   g_term_y[k],
									   uncommon_term_c_choose[l][k]);
						break;
					}
				}
			}
		}

		/*Debug Criterion for GS Decoding*/
		if((S_MUL * (CODEWORD_LEN - err_num)) > uncommon_weight_pol_1_k_1[l][sml_poly])
		{
			DEBUG_NOTICE("decoding_ok_flag: %d %d %d\n",
				         decoding_ok_flag,
				         (S_MUL * (CODEWORD_LEN - err_num)),
				         uncommon_weight_pol_1_k_1[l][sml_poly]);
			if(0 == decoding_ok_flag)
			{
				decoding_ok_flag = 1;
				DEBUG_NOTICE("decoding_ok_flag = 1!\n");
			}
			weight_stored = uncommon_weight_pol_1_k_1[l][sml_poly];
		}
	}

#if (CFG_RR_MODE >= CONV_RE_ENC_SYS)
	unsigned char tmp_product[term_size_x * term_size_y];
	unsigned char tmp_v[term_size_x * term_size_y];
	unsigned char tmp_q0[term_size_x * term_size_y];
	unsigned char tmp_q1[term_size_x * term_size_y];
	memset(tmp_product, 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));
	memset(tmp_v, 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));
	memset(tmp_q0, 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));
	memset(tmp_q1, 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));

	j = 0;
	for(i = 0; i < (term_size_x * term_size_y); i++)
	{
		if(j == g_term_x[i])
		{
			tmp_v[i] = v[j];
			j++;
		}
		if(j >= (MESSAGE_LEN + 1))
		{
			break;
		}
	}

	for(i = 0; i < (term_size_x * term_size_y); i++)
	{
		if((0xFF != uncommon_term_c_choose[l][i])
			&& (0 == g_term_y[i]))
		{
			tmp_q0[i] = uncommon_term_c_choose[l][i];
		}
	}

	for(i = 0; i < (term_size_x * term_size_y); i++)
	{
		if((0xFF != uncommon_term_c_choose[l][i])
			&& (0 != g_term_y[i]))
		{
			tmp_q1[i] = uncommon_term_c_choose[l][i];
		}
	}

	poly_mul(tmp_q0,
			 tmp_v,
			 tmp_product,
			 term_size_x * term_size_y);

	for(i = 0; i < (term_size_x * term_size_y); i++)
	{
		if(0 != g_term_y[i])
		{
			tmp_product[i] = gf_add(tmp_product[i], uncommon_term_c_choose[l][i]);
		}
		if(0xFF != tmp_product[i])
		{
			DEBUG_NOTICE("tmp_product: %ld %ld | %x\n",
						 g_term_x[i],
						 g_term_y[i],
						 tmp_product[i]);

			if(g_term_x[i] > max_dx)
			{
				max_dx = g_term_x[i];
				//DEBUG_SYS("max_dx: %ld\n", max_dx);
			}
			if(g_term_y[i] > max_dy)
			{
				max_dy = g_term_y[i];
				//DEBUG_SYS("max_dy: %ld\n", max_dy);
			}
		}
	}
	memcpy(uncommon_term_c_choose[l], tmp_product, sizeof(unsigned char) * (term_size_x * term_size_y));
#endif

	free(g_table_x);
	g_table_x = NULL;
	free(g_table_y);
	g_table_y = NULL;
	free(discrepancy);
	discrepancy = NULL;
	free(tmp_table_c);
	tmp_table_c = NULL;
	
	return 0;
}

long long uncommon_check_decoded_result()
{
	long long i = 0, j = 0, l = 0;
	
	long long hamm_distance = 0;
	long long best_hamm_distance = 0x7FFF;
	long long best_place = 0;
	
	for(l = 0; l < pow_val; l++)
	{
		hamm_distance = 0;
#if (0 == SYS_ENC)	
		for(i = 0; i < CODEWORD_LEN; i++)
		{
			if(uncommon_decoded_codeword[l][i] != encoded_polynomial[i])
			{
				hamm_distance = hamm_distance + 1;
				DEBUG_INFO("hamm_distance_ongoing: %d | %d | %x %x | %d\n",
				           l,
				           i,
				           uncommon_decoded_codeword[l][i],
				           encoded_polynomial[i],
				           hamm_distance);
			}
		}
#else
		for(i = 0; i < MESSAGE_LEN; i++)
		{
			if(uncommon_decoded_codeword[l][i + (CODEWORD_LEN - MESSAGE_LEN)] != message_polynomial[i])
			{
				hamm_distance = hamm_distance + 1;
				DEBUG_INFO("hamm_distance_ongoing: %d | %d | %x %x | %d\n",
				           l,
				           i,
				           uncommon_decoded_codeword[l][i + (CODEWORD_LEN - MESSAGE_LEN)],
				           message_polynomial[i],
				           hamm_distance);
			}
		}
#endif

		DEBUG_INFO("hamm_distance: %d | %d\n",
		           l,
		           hamm_distance);

		if(best_hamm_distance > hamm_distance)
		{
			best_hamm_distance = hamm_distance;
			best_place = l;
		}
	}

	return best_place;
}

#if (1 == CFG_STORE_PARALEL)
int store_q_poly_save(long long batch_idx, long long tst_vct_idx)
{
	long long i = 0, j = 0;
	
	for(i = 0; i < d_y_num; i++)
	{
		for(j = 0; j < term_size_p; j++)
		{
			store_uncommon_table_c_prev[batch_idx][i][j] = uncommon_table_c_prev[tst_vct_idx][i][j];
			if(0xFF != store_uncommon_table_c_prev[batch_idx][i][j])
			{
				DEBUG_NOTICE("save: %ld %ld| %ld | %ld | %ld\n",
				          	 batch_idx,
				          	 tst_vct_idx,
				          	 i,
				          	 j,
				          	 store_uncommon_table_c_prev[batch_idx][i][j]);
			}
		}
	}
	
	return 0;
}

int store_q_poly_load(long long batch_idx, long long tst_vct_idx)
{
	long long i = 0, j = 0;
	
	for(i = 0; i < d_y_num; i++)
	{
		for(j = 0; j < term_size_p; j++)
		{
			uncommon_table_c_prev[tst_vct_idx][i][j] = store_uncommon_table_c_prev[batch_idx][i][j];
			if(0xFF != store_uncommon_table_c_prev[batch_idx][i][j])
			{
				DEBUG_NOTICE("load: %ld %ld| %ld | %ld | %ld\n",
					      	 batch_idx,
					      	 tst_vct_idx,
						     i,
						     j,
						     store_uncommon_table_c_prev[batch_idx][i][j]);
			}
		}
	}
	
	return 0;
}
#endif

#if (1 == CFG_IMD_STORE)
int store_q_c_save(long long layer_idx, long long node_idx, long long tst_vct_idx)
{
	long long i = 0, j = 0, k = 0, l = 0;
	long long save_cnt = 0, save_start = 0;
	
	for(i = 0; i < d_y_num; i++)
	{
		for(j = 0; j < term_size_p; j++)
		{
			store_q_c_prev[layer_idx][node_idx][i][j] = uncommon_table_c_prev[tst_vct_idx][i][j];
			if(0xFF != store_q_c_prev[layer_idx][node_idx][i][j])
			{
				DEBUG_NOTICE("save: %ld %ld | %ld | %ld | %ld | %d\n",
				          	 layer_idx,
				          	 node_idx,
				          	 tst_vct_idx,
				          	 i,
				          	 j,
				          	 store_q_c_prev[layer_idx][node_idx][i][j]);
			}
		}
	}
	
	store_q_c_flag[layer_idx][node_idx] = 1;

	save_cnt = (long long)pow(2, YITA - layer_idx - 1);
	save_start = (long long)floor(tst_vct_idx / save_cnt) * save_cnt;
	DEBUG_INFO("save_cnt: %ld %ld\n", save_cnt, save_start);

	for(k = save_start; k < save_start + save_cnt; k++)
	{
		if(node_idx == k)
		{
			continue;
		}
		if(1 == store_q_c_flag[layer_idx][k])
		{
			continue;
		}
		for(i = 0; i < d_y_num; i++)
		{
			for(j = 0; j < term_size_p; j++)
			{
				store_q_c_prev[layer_idx][k][i][j] = uncommon_table_c_prev[tst_vct_idx][i][j];
				if(0xFF != store_q_c_prev[layer_idx][k][i][j])
				{
					DEBUG_NOTICE("save_expand: %ld %ld | %ld | %ld | %ld | %d\n",
					          	 layer_idx,
					          	 k,
					          	 tst_vct_idx,
					          	 i,
					          	 j,
					          	 store_q_c_prev[layer_idx][k][i][j]);
				}
			}
		}
		store_q_c_flag[layer_idx][k] = 1;
	}

	return 0;
}

int store_q_c_load(long long layer_idx, long long node_idx, long long tst_vct_idx)
{
	long long i = 0, j = 0;
	
	for(i = 0; i < d_y_num; i++)
	{
		for(j = 0; j < term_size_p; j++)
		{
#if 0		
			if(uncommon_table_c_prev[tst_vct_idx][i][j] != store_q_c_prev[layer_idx][node_idx][i][j])
			{
				DEBUG_NOTICE("load err: %ld %ld | %ld | %ld | %ld | %d %d\n",
				          	 layer_idx,
				          	 node_idx,
				          	 tst_vct_idx,
				          	 i,
				          	 j,
				          	 uncommon_table_c_prev[tst_vct_idx][i][j],
				          	 store_q_c_prev[layer_idx][node_idx][i][j]);
			}
#endif			
			uncommon_table_c_prev[tst_vct_idx][i][j] = store_q_c_prev[layer_idx][node_idx][i][j];
			uncommon_term_c_p[tst_vct_idx][i][j] = uncommon_table_c_prev[tst_vct_idx][i][j];
			if(0xFF != uncommon_table_c_prev[tst_vct_idx][i][j])
			{
				DEBUG_NOTICE("load: %ld %ld | %ld | %ld | %ld | %d\n",
				          	 layer_idx,
				          	 node_idx,
				          	 tst_vct_idx,
				          	 i,
				          	 j,
				          	 uncommon_table_c_prev[tst_vct_idx][i][j]);
			}
		}
	}
	
	return 0;
}
#endif

int fast_err_in_r_get(long long l)
{
	long long i = 0, j = 0;
	unsigned char q1[CODEWORD_LEN];
	memset(q1, 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
	unsigned char tmp_q1[term_size_x * term_size_y];
	memset(tmp_q1, 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));
	unsigned char q1_val = 0xFF;
	
	for(i = 0; i < (term_size_x * term_size_y); i++)
	{
		if((0xFF != uncommon_term_c_choose[l][i])
			&& (0 != g_term_y[i]))
		{
			tmp_q1[i] = uncommon_term_c_choose[l][i];
		}
	}
	
	for(i = 0; i < (term_size_x * term_size_y); i++)
	{
		if(0xFF != tmp_q1[i])
		{
			DEBUG_NOTICE("q1: %d %d| %x\n", g_term_x[i], g_term_y[i], tmp_q1[i]);
			q1[g_term_x[i]] = tmp_q1[i];
		}
	}
	
	for(i = 0; i < CODEWORD_LEN; i++)
	{
		q1_val = poly_eva(q1,
			              CODEWORD_LEN,
			              power_polynomial_table[i + 1][0]);
		                  
		if(0xFF == q1_val)
		{
			for(j = 0; j < MESSAGE_LEN; j++)
			{
				if(i == rel_group_seq[j])
				{
					DEBUG_SYS("q1_val: %d | %x | %x %x\n",
							  i,
					          q1_val,
					          encoded_polynomial[i],
					          received_polynomial[i]);
				}
			}
		}		   
	}

	return 0;
}

int fast_root_finding_skip(long long l)
{
	long long i = 0;
	unsigned char q0[CODEWORD_LEN], q1[CODEWORD_LEN];
	unsigned char tmp_q0[term_size_x * term_size_y], tmp_q1[term_size_x * term_size_y];
	long long degree_q0 = -1;
	
	memset(q0, 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
	memset(tmp_q0, 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));
	memset(q1, 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
	memset(tmp_q1, 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));
	
	for(i = 0; i < (term_size_x * term_size_y); i++)
	{
		if((0xFF != uncommon_term_c_choose[l][i])
			&& (0 == g_term_y[i]))
		{
			tmp_q0[i] = uncommon_term_c_choose[l][i];
		}
	}
	
	for(i = 0; i < (term_size_x * term_size_y); i++)
	{
		if((0xFF != uncommon_term_c_choose[l][i])
			&& (0 != g_term_y[i]))
		{
			tmp_q1[i] = uncommon_term_c_choose[l][i];
		}
	}
	
	for(i = 0; i < (term_size_x * term_size_y); i++)
	{
		if(0xFF != tmp_q0[i])
		{
			DEBUG_NOTICE("q0: %d %d| %x\n", g_term_x[i], g_term_y[i], tmp_q0[i]);
			q0[g_term_x[i]] = tmp_q0[i];
			degree_q0 = g_term_x[i];
		}
	}
	DEBUG_NOTICE("degree_q0: %ld\n", degree_q0);
	
	for(i = 0; i < (term_size_x * term_size_y); i++)
	{
		if(0xFF != tmp_q1[i])
		{
			DEBUG_NOTICE("q1: %d %d| %x\n", g_term_x[i], g_term_y[i], tmp_q1[i]);
			q1[g_term_x[i]] = tmp_q1[i];
		}
	}
	
	if(-1 == degree_q0)
	{
#if 0	
		unsigned char q1_val = poly_eva(q1,
								  	    CODEWORD_LEN,
								  	    power_polynomial_table[i + 1][0]);
					  	 
		if(0xFF != q1_val)
		{
#endif		
			memcpy(uncommon_decoded_codeword[l], phi, sizeof(unsigned char) * CODEWORD_LEN);

			return 1;
#if 0			
		}
		else
		{
			return 0;
		}
#endif		
	}
	else
	{
		return 0;
	}
}

int bf_polynomial_process(unsigned char locator, unsigned char **poly, unsigned char **poly_back)
{
	long long i = 0, j = 0;
	long long u = 0, v = 1;
	
	unsigned char q0[d_y_num][CODEWORD_LEN], q1[d_y_num][CODEWORD_LEN];
	unsigned char tmp_q0[d_y_num][term_size_x * term_size_y], tmp_q1[d_y_num][term_size_x * term_size_y];
	unsigned char q1_val[d_y_num];
	long long g_weight[d_y_num];
	
	DEBUG_NOTICE("%s\n", __func__);
	
	for(i = 0; i < d_y_num; i++)
	{
		memset(q1[i], 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
		memset(tmp_q1[i], 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));
		memset(q0[i], 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
		memset(tmp_q0[i], 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));
	}
	memset(q1_val, 0xFF, sizeof(unsigned char) * d_y_num);
	memset(g_weight, 0, sizeof(long long) * d_y_num);
	
	for(i = 0; i < d_y_num; i++)
	{
		for(j = 0; j < (term_size_x * term_size_y); j++)
		{
			if((0xFF != poly[i][j])
				&& (0 != g_term_y[j]))
			{
				tmp_q1[i][j] = poly[i][j];
			}
		}
	}
	
	for(i = 0; i < d_y_num; i++)
	{
		for(j = 0; j < (term_size_x * term_size_y); j++)
		{
			if(0xFF != tmp_q1[i][j])
			{
				DEBUG_NOTICE("q1: %d %d | %x\n", g_term_x[j], g_term_y[j], tmp_q1[i][j]);
				q1[i][g_term_x[j]] = tmp_q1[i][j];
				
				/*the lexorder should be considered later, just do it like this now*/
				if(g_weight[i] < (g_term_x[j] + (MESSAGE_LEN - 1) * g_term_y[j]))
				{
					g_weight[i] = g_term_x[j] + (MESSAGE_LEN - 1) * g_term_y[j];
				}
			}
		}
		q1_val[i] = poly_eva(q1[i], CODEWORD_LEN, locator);
		DEBUG_NOTICE("q1_para: %x %ld\n", q1_val[i], g_weight[i]);
	}
	
	if((0xFF == q1_val[0])
	   && (0xFF != q1_val[1]))
	{
		u = 1;
		v = 0;
	}
	else if((0xFF != q1_val[0])
	   		&& (0xFF == q1_val[1]))
	{
		u = 0;
		v = 1;
	}
	else if(g_weight[0] > g_weight[1])
	{
		u = 0;
		v = 1;
	}
	else
	{
		u = 1;
		v = 0;
	}
	DEBUG_NOTICE("u & v: %ld %ld\n", u, v);
	
	if(0xFF != q1_val[v])
	{
		for(i = 0; i < (term_size_x * term_size_y); i++)
		{
			if((0xFF != poly[v][i])
			   || (0xFF != poly[u][i]))
			{
				poly[v][i] = gf_multp(poly[v][i], q1_val[u])
						   + gf_multp(poly[u][i], q1_val[v]);
				DEBUG_NOTICE("poly[v]: %ld | %ld %ld | %ld\n",
				              i,
				              g_term_x[i],
				              g_term_y[i],
				              poly[v][i]);		   
			}
		}
	}
	
	for(i = 0; i < d_y_num; i++)
	{
		memset(q1[i], 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
		memset(tmp_q1[i], 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));
		memset(q0[i], 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
		memset(tmp_q0[i], 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));
	}

	for(i = 0; i < (term_size_x * term_size_y); i++)
	{
		if((0xFF != poly[v][i])
			&& (0 == g_term_y[i]))
		{
			tmp_q0[v][i] = poly[v][i];
		}
	}

	for(i = 0; i < (term_size_x * term_size_y); i++)
	{
		if((0xFF != poly[v][i])
			&& (0 != g_term_y[i]))
		{
			tmp_q1[v][i] = poly[v][i];
		}
	}

	for(i = 0; i < (term_size_x * term_size_y); i++)
	{
		if(0xFF != tmp_q0[v][i])
		{
			DEBUG_NOTICE("q0: %d %d| %x\n", g_term_x[i], g_term_y[i], tmp_q0[v][i]);
			q0[v][g_term_x[i]] = tmp_q0[v][i];
		}
	}

	for(i = 0; i < (term_size_x * term_size_y); i++)
	{
		if(0xFF != tmp_q1[v][i])
		{
			DEBUG_NOTICE("q1: %d %d| %x\n", g_term_x[i], g_term_y[i], tmp_q1[v][i]);
			q1[v][g_term_x[i]] = tmp_q1[v][i];
		}
	}
	
	unsigned char q0_div_cof[CODEWORD_LEN],  q1_div_cof[CODEWORD_LEN];
	memset(q0_div_cof, 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
	memset(q1_div_cof, 0xFF, sizeof(unsigned char) * CODEWORD_LEN);

	//q0_div_cof[CODEWORD_LEN - 2] = q0[v][CODEWORD_LEN - 1];
	for(i = CODEWORD_LEN - 1; i > 0; i--)
	{
		q0_div_cof[i - 1] = gf_add(q0[v][i],
		                           gf_multp(locator, q0_div_cof[i]));
		if(0xFF != q0_div_cof[i - 1])
		{
			DEBUG_NOTICE("q0_div_cof: %d | %d %d | %d %d | %d\n",
			             i - 1,
			             locator,
			             q0_div_cof[i],
			             gf_multp(locator, q0_div_cof[i]),
			             q0[v][i],
			             q0_div_cof[i - 1]);
		}
		
		q1_div_cof[i - 1] = gf_add(q1[v][i],
		                           gf_multp(locator, q1_div_cof[i]));
		if(0xFF != q1_div_cof[i - 1])
		{
			DEBUG_NOTICE("q1_div_cof: %d | %d %d | %d %d | %d\n",
			             i - 1,
			             locator,
			             q1_div_cof[i],
			             gf_multp(locator, q1_div_cof[i]),
			             q1[v][i],
			             q1_div_cof[i - 1]);
		}
	}
	
	for(i = 0; i < (term_size_x * term_size_y); i++)
	{
		if((CODEWORD_LEN - 1) < g_term_x[i])
		{
			break;
		}
		poly_back[v][i] = 0xFF;
	
		if((0xFF != q0_div_cof[g_term_x[i]])
			&& (0 == g_term_y[i]))
		{
			poly_back[v][i] = q0_div_cof[g_term_x[i]];
		}
		
		if((0xFF != q1_div_cof[g_term_x[i]])
			&& (1 == g_term_y[i]))
		{
			poly_back[v][i] = q1_div_cof[g_term_x[i]];
		}
		
		if(0xFF != poly_back[v][i])
		{
			DEBUG_NOTICE("poly[v][i]: %d %d | %d\n", 
			             g_term_x[i],
			             g_term_y[i],
			             poly_back[v][i]);
		}
	}

	return 0;
}

#if (1 == FAST_RR_M1_DBG)
unsigned char tmp_test[CODEWORD_LEN - MESSAGE_LEN];
#endif

#if (1 == RE_ENCODING)
#if (CFG_RR_MODE == FAST_RR_M1)
int uncommon_fast_msg_get(long long l)
{
	long long i = 0, j = 0;
	//long long l = 0;
	long long best_place = pow_val;

	unsigned char q0[CODEWORD_LEN], q1[CODEWORD_LEN];
	unsigned char q0_dev[CODEWORD_LEN], q1_dev[CODEWORD_LEN], v_dev[MESSAGE_LEN + 1];
	unsigned char rec_dir_cw[CODEWORD_LEN];
	unsigned char tmp_v[term_size_x * term_size_y];
	unsigned char tmp_q0[term_size_x * term_size_y];
	unsigned char tmp_q1[term_size_x * term_size_y];
	unsigned char v_val = 0xFF, q1_val = 0xFF, q0_val = 0xFF;
	
	long long degree_q0 = -1, degree_q1 = -1;

	unsigned char parity_seq[CODEWORD_LEN - MESSAGE_LEN];
	for(i = 0; i < (CODEWORD_LEN - MESSAGE_LEN); i++)
	{
		parity_seq[i] = i;
	}

	//for(l = 0; l < pow_val; l++)
	{

#if 0
		int tst_skip_cnt = CODEWORD_LEN;
		tst_skip_cnt = CODEWORD_LEN;
		for(i = 0; i < l; i++)
		{
			tst_skip_cnt = fast_check_tst_vct_radius(i, l);
			DEBUG_INFO("tst_skip_cnt: %d\n", tst_skip_cnt);
			if(((CODEWORD_LEN - MESSAGE_LEN) / 2) >= tst_skip_cnt)
			{
				break;
			}
		}
		if(((CODEWORD_LEN - MESSAGE_LEN) / 2) >= tst_skip_cnt)
		{
			DEBUG_INFO("tst_vct_skip: %d %d\n", l, tst_skip_cnt);
			continue;
		}
#endif

		memset(q0, 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
		memset(q1, 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
		memset(q0_dev, 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
		memset(q1_dev, 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
		memset(v_dev, 0xFF, sizeof(unsigned char) * (MESSAGE_LEN + 1));
		memset(rec_dir_cw, 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
		memset(tmp_v, 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));
		memset(tmp_q0, 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));
		memset(tmp_q1, 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));

		for(i = 0; i < (term_size_x * term_size_y); i++)
		{
			if((0xFF != uncommon_term_c_choose[l][i])
				&& (0 == g_term_y[i]))
			{
				tmp_q0[i] = uncommon_term_c_choose[l][i];
			}
		}

		for(i = 0; i < (term_size_x * term_size_y); i++)
		{
			if((0xFF != uncommon_term_c_choose[l][i])
				&& (0 != g_term_y[i]))
			{
				tmp_q1[i] = uncommon_term_c_choose[l][i];
			}
		}

		for(i = 0; i < (term_size_x * term_size_y); i++)
		{
			if(0xFF != tmp_q0[i])
			{
				DEBUG_NOTICE("q0: %d %d| %x\n", g_term_x[i], g_term_y[i], tmp_q0[i]);
				q0[g_term_x[i]] = tmp_q0[i];
				degree_q0 = g_term_x[i];
			}
		}
		DEBUG_NOTICE("degree_q0: %ld\n", degree_q0);

		for(i = 0; i < (term_size_x * term_size_y); i++)
		{
			if(0xFF != tmp_q1[i])
			{
				DEBUG_NOTICE("q1: %d %d| %x\n", g_term_x[i], g_term_y[i], tmp_q1[i]);
				q1[g_term_x[i]] = tmp_q1[i];
				degree_q1 = g_term_x[i];
			}
		}
		DEBUG_NOTICE("degree_q1: %ld\n", degree_q1);

		for(i = 0; i < CODEWORD_LEN; i++)
		{
			DEBUG_NOTICE("q: %ld | %x %x\n", i, q0[i], q1[i]);
		}
		
		unsigned char have_root = 1;
#if (1 == CFG_Y_ROOTS_SKIP)
		unsigned char tmp_q1_poly_val[CODEWORD_LEN];
		memset(tmp_q1_poly_val, 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
		unsigned char q1_root_cnt = 0xFF;
		for(i = 0; i < CODEWORD_LEN; i++)
		{
			tmp_q1_poly_val[i] = poly_eva(q1,
										  CODEWORD_LEN,
										  power_polynomial_table[i + 1][0]);
			if(0xFF == tmp_q1_poly_val[i])
			{
				q1_root_cnt++;
			}
		}
		unsigned char tmp_q1_0 = 0;
		tmp_q1_0 = poly_eva(q1,
							CODEWORD_LEN,
							power_polynomial_table[0][0]);;
		if(0xFF == tmp_q1_0)
		{
			q1_root_cnt++;
		}
		long long err_num = 0, diff_num = 0;
		for(i = 0; i < CODEWORD_LEN; i++)
		{
			//DEBUG_SYS("compare: %ld | %x %x\n", i, encoded_polynomial[i], tst_vct[l][i]);
			if(encoded_polynomial[i] != tst_vct[l][i])
			{
				err_num++;
			}
			if(received_polynomial[i] != tst_vct[l][i])
			{
				diff_num++;
			}
		}
		if(q1_root_cnt < degree_q1)
		{
			have_root = 0;
			//return 0;
			if(0 == l)
			{
				//DEBUG_SYS("Y_ROOTS_SKIP_DET: %ld | %ld %ld | %ld %ld\n", l, q1_root_cnt, degree_q1, err_num, diff_num);
				g_decoded_cnt = pow_val + 1;
			}
			else
			{
				if((pow_val + 1) <= g_decoded_cnt)
				{
					//DEBUG_SYS("Y_ROOTS_SKIP_DET: %ld | %ld %ld | %ld %ld\n", l, q1_root_cnt, degree_q1, err_num, diff_num);
					g_decoded_cnt++;
				}
			}
		}
		DEBUG_NOTICE("Y_ROOTS_SKIP: %ld | %ld %ld | %ld %ld\n", l, q1_root_cnt, degree_q1, err_num, diff_num);
#endif
		
#if 0
		for(i = 0; i < CODEWORD_LEN; i++)
		{
			if(i < (CODEWORD_LEN - MESSAGE_LEN))
			{
				uncommon_decoded_codeword[l][i] = 0xFF;
				//continue;
			}
		
			q0_val = poly_eva(q0,
				              CODEWORD_LEN,
				              power_polynomial_table[i + 1][0]);
#if 0
			v_val = poly_eva(v,
				             (MESSAGE_LEN + 1),
				             power_polynomial_table[i + 1][0]);
#else				             
			v_val = g_v_val[i];
#endif			
			q1_val = poly_eva(q1,
			                  CODEWORD_LEN,
			                  power_polynomial_table[i + 1][0]);
			if(0xFF != q1_val)
			{
				rec_dir_cw[i] = gf_div(gf_multp(q0_val, v_val),
									   q1_val);
			}
			else//there are some problems now
			{
				for(j = 0; j < CODEWORD_LEN; j++)
				{
					if(0 != (j % 2))
					{
						q1_dev[j - 1] = q1[j];
					}
					else
					{
						q1_dev[j - 1] = 0xFF;
					}
				}
				q1_val = poly_eva(q1_dev,
				                  CODEWORD_LEN,
				              	  power_polynomial_table[i + 1][0]);
				
				if(0xFF == v_val)
				{
					for(j = 1; j < (MESSAGE_LEN + 1); j++)
					{
						if(0 != (j % 2))
						{
							v_dev[j - 1] = v[j];
						}
						DEBUG_NOTICE("v_dev: %ld | %x\n", j - 1, v_dev[j - 1]);
					}

					v_val = poly_eva(v_dev,
				             		 (MESSAGE_LEN + 1),
				             		 power_polynomial_table[i + 1][0]);

					rec_dir_cw[i] = gf_div(gf_multp(q0_val, v_val),
									       q1_val);
				}

				if(0xFF == q0_val)
				{
					for(j = 1; j < (MESSAGE_LEN + 1); j++)
					{
						if(0 != (j % 2))
						{
							q0_dev[j - 1] = q0[j];
						}
						DEBUG_NOTICE("q0_dev: %ld | %x\n", j - 1, q0_dev[j - 1]);
					}

					q0_val = poly_eva(q0_dev,
				             		 CODEWORD_LEN,
				             		 power_polynomial_table[i + 1][0]);

					rec_dir_cw[i] = gf_div(gf_multp(q0_val, v_val),
									       q1_val);
				}
			}

			uncommon_decoded_codeword[l][i] = gf_add(rec_dir_cw[i], phi[i]);

			DEBUG_NOTICE("rec_dir_cw: %d | %d | %x*%x/%x=%x | %x\n",
			             l,
				         i,
				         v_val,
				         q0_val,
				         q1_val,
				         rec_dir_cw[i],
				         uncommon_decoded_codeword[l][i]);
		}
#else
#if (1 == FAST_RR_M1_DBG)
		memset(tmp_test, 0xFF, sizeof(unsigned char) * (CODEWORD_LEN - MESSAGE_LEN));
#endif
		for(i = 0; i < CODEWORD_LEN; i++)
		{
			q1_val = 0xFF;

			if(i < (CODEWORD_LEN - MESSAGE_LEN))
			{
#if (0 == FAST_RR_M1_DBG)		
				continue;
#endif
			}
#if 1
			best_place = pow_val;
			for(j = 0; j < (CODEWORD_LEN - MESSAGE_LEN); j++)
			{
				if(i == unrel_group_seq[j])
				{
					best_place = -1;
					break;
				}
			}
			if(-1 == best_place)
			{
				uncommon_decoded_codeword[l][i] = 0xFF;
				continue;
			}
#endif			

#if (1 == CFG_Q0_FAST_SKIP)		
			if((-1) == degree_q0)
			{
#if 0
				q1_val = poly_eva(q1,
							  	  CODEWORD_LEN,
							  	  power_polynomial_table[i + 1][0]);
				if(0xFF == q1_val)
				{
					DEBUG_INFO("q0_q1_err: %ld\n", power_polynomial_table[i + 1][0]);
				}
			
				if(0xFF != q1_val)
#endif				
				{
					uncommon_decoded_codeword[l][i] = phi[i];
#if (1 == FAST_RR_M1_DBG)					
					if(i < (CODEWORD_LEN - MESSAGE_LEN))
					{
						tmp_test[i] = uncommon_decoded_codeword[l][i];
					}
#endif				
					DEBUG_INFO("degree_q0_skip\n");
					continue;
				}
			}
#endif			

			if((-1) != degree_q0)
			{
				q1_val = poly_eva(q1,
								  CODEWORD_LEN,
								  power_polynomial_table[i + 1][0]);
			}

#if 0
			v_val = poly_eva(v,
				             (MESSAGE_LEN + 1),
				             power_polynomial_table[i + 1][0]);
#else				             
			v_val = g_v_val[i];
#endif
			if((0xFF != q1_val)
			   && (0xFF == v_val))
			{
				uncommon_decoded_codeword[l][i] = phi[i];
#if (1 == FAST_RR_M1_DBG)				
				if(i < (CODEWORD_LEN - MESSAGE_LEN))
				{
					tmp_test[i] = uncommon_decoded_codeword[l][i];
				}
#endif
				DEBUG_INFO("v_skip: %x\n", i);
				continue;
			}
			q0_val = poly_eva(q0,
				              CODEWORD_LEN,
				              power_polynomial_table[i + 1][0]);		

#if 0			                  
			if(0xFF == q1_val)
			{
				for(j = 0; j < MESSAGE_LEN; j++)
				{
					if(i == rel_group_seq[j])
					{
						DEBUG_SYS("q1_val: %d | %x | %x %x\n",
								  i,
						          q1_val,
						          encoded_polynomial[i],
						          received_polynomial[i]);
					}
				}
			}
#endif

			if(0xFF != q1_val)
			{
				rec_dir_cw[i] = gf_div(gf_multp(q0_val, v_val),
								   	   q1_val);
			}
			else//there are some problems now
			{
				for(j = 0; j < CODEWORD_LEN; j++)
				{
					if(0 != (j % 2))
					{
						q1_dev[j - 1] = q1[j];
					}
					else
					{
						q1_dev[j - 1] = 0xFF;
					}
				}
				q1_val = poly_eva(q1_dev,
				                  CODEWORD_LEN,
				              	  power_polynomial_table[i + 1][0]);
				
				if((0xFF == q0_val)
					&& (0xFF == v_val))
				{
					DEBUG_SYS("Facr. free Err.!!!!!!!!\n");
				}

				if(0xFF == v_val)
				{
					for(j = 1; j < (MESSAGE_LEN + 1); j++)
					{
						if(0 != (j % 2))
						{
							v_dev[j - 1] = v[j];
						}
						DEBUG_NOTICE("v_dev: %ld | %x\n", j - 1, v_dev[j - 1]);
					}

					v_val = poly_eva(v_dev,
				             		 (MESSAGE_LEN + 1),
				             		 power_polynomial_table[i + 1][0]);

					rec_dir_cw[i] = gf_div(gf_multp(q0_val, v_val),
									       q1_val);
				}

				if(0xFF == q0_val)
				{
					for(j = 1; j < (MESSAGE_LEN + 1); j++)
					{
						if(0 != (j % 2))
						{
							q0_dev[j - 1] = q0[j];
						}
						DEBUG_NOTICE("q0_dev: %ld | %x\n", j - 1, q0_dev[j - 1]);
					}

					q0_val = poly_eva(q0_dev,
				             		 CODEWORD_LEN,
				             		 power_polynomial_table[i + 1][0]);

					rec_dir_cw[i] = gf_div(gf_multp(q0_val, v_val),
									       q1_val);
				}
			}

			uncommon_decoded_codeword[l][i] = gf_add(rec_dir_cw[i], phi[i]);
#if (1 == FAST_RR_M1_DBG)
			if(i < (CODEWORD_LEN - MESSAGE_LEN))
			{
				tmp_test[i] = uncommon_decoded_codeword[l][i];
			}
#endif			
			DEBUG_NOTICE("rec_dir_cw: %d | %d | %x*%x/%x=%x | %x\n",
			             l,
				         i,
				         v_val,
				         q0_val,
				         q1_val,
				         rec_dir_cw[i],
				         uncommon_decoded_codeword[l][i]);
		}

#if 1
		erasure_decoding_use(uncommon_decoded_codeword[l], unrel_group_seq);
		//memcpy(uncommon_decoded_codeword[l], phi, sizeof(unsigned char) * CODEWORD_LEN);
		memcpy(tmp_test, uncommon_decoded_codeword[l], sizeof(unsigned char) * (CODEWORD_LEN - MESSAGE_LEN));
#endif
		memcpy(uncommon_decoded_message[l], uncommon_decoded_codeword[l] + (CODEWORD_LEN - MESSAGE_LEN), sizeof(unsigned char) * MESSAGE_LEN);

#if 0//(1 == CFG_FAST_SKIP_TST_VCT)
		encoding3(uncommon_decoded_message[l], uncommon_decoded_codeword[l]);
#endif
#if (1 == CFG_PARTIALLY_PARALLEL)
#if 0//(1 == CFG_PARALLEL_FAST_SKIP)//notice this
		encoding3(uncommon_decoded_message[l], uncommon_decoded_codeword[l]);
#endif
#endif
#endif
#if (1 == FAST_RR_M1_DBG)
		for(i = 0; i < (CODEWORD_LEN - MESSAGE_LEN); i++)
		{
			if(uncommon_decoded_codeword[l][i] != tmp_test[i])
			{
				DEBUG_NOTICE("Facr. free Err.: %ld %ld | %x %x\n", l, i, uncommon_decoded_codeword[l][i], tmp_test[i]);
				best_place = -1;
				break;
			}
		}
		if(-1 == best_place)
		{
			for(i = 0; i < CODEWORD_LEN; i++)
			{
				DEBUG_NOTICE("test cw: %ld | %x %x\n",
						  i,
						  encoded_polynomial[i],
						  received_polynomial[i]);
			}
			for(i = 0; i < CODEWORD_LEN; i++)
			{
				DEBUG_NOTICE("decoded cw: %ld | %x %x\n",
						  i,
						  uncommon_decoded_codeword[l][i],
						  tmp_test[i]);
			}
			for(i = 0; i < MESSAGE_LEN; i++)
			{
				DEBUG_NOTICE("msg: %ld | %x\n",
						  i,
						  message_polynomial[i]);
			}
			for(i = 0; i < MESSAGE_LEN; i++)
			{
				DEBUG_NOTICE("rel_gp: %ld | %x\n",
						  i,
						  rel_group_seq[i]);
			}
			for(i = 0; i < CODEWORD_LEN; i++)
			{
				DEBUG_NOTICE("test vct: %ld | %x\n",
						  i,
						  tst_vct[l][i]);
			}
		}
#endif		
		//erasure_decoding(uncommon_decoded_codeword[l], parity_seq);
		//memcpy(uncommon_decoded_codeword[l], phi, sizeof(unsigned char) * CODEWORD_LEN);
		float output_rel_sum = 0, input_rel_sum = 0;
		long long tmp_cnt = 0;
		for(i = 0; i < CODEWORD_LEN; i++)
		{
			DEBUG_NOTICE("decoded_codeword_get: %d | %d | %x | %x\n",
			             l,
				         i,
				         uncommon_decoded_codeword[l][i],
				         phi[i]);
			if(0xFF == uncommon_decoded_codeword[l][i])
			{
				output_rel_sum = output_rel_sum + chnl_rel_matrix[0][i];	
			}
			else
			{
				output_rel_sum = output_rel_sum + chnl_rel_matrix[uncommon_decoded_codeword[l][i] + 1][i];	
			}
			if(0xFF == tst_vct[l][i])
			{
				input_rel_sum = input_rel_sum + chnl_rel_matrix[0][i];	
			}
			else
			{
				input_rel_sum = input_rel_sum + chnl_rel_matrix[tst_vct[l][i] + 1][i];	
			}
			if(tst_vct[l][i] != encoded_polynomial[i])
			{
				tmp_cnt++;
				DEBUG_INFO("err_obsv: %ld %ld | %x %x\n", l, i, tst_vct[l][i], encoded_polynomial[i]);
			}
		}
		DEBUG_INFO("output_rel_sum: %ld | %f | %f %f | %ld | %d\n", l, tst_vct_rel[l], input_rel_sum, output_rel_sum, tmp_cnt, have_root);
	}

#if 0
	best_place = uncommon_check_decoded_result();
	memcpy(decoded_codeword, uncommon_decoded_codeword[best_place], sizeof(unsigned char) * CODEWORD_LEN);
	memcpy(decoded_message, decoded_codeword + (CODEWORD_LEN - MESSAGE_LEN), sizeof(unsigned char) * MESSAGE_LEN);

	for(i = 0; i < MESSAGE_LEN; i++)
	{
		DEBUG_IMPOTANT("uncommon_decoded_message: %d | %d | %x\n",
		               best_place,
		               i,
		               decoded_message[i]);
	}
	if(0 != best_place)
	{
		DEBUG_SYS("Best Place: %ld\n", best_place);
	}
#endif

	return 0;
}
#endif

#if 1//(CFG_RR_MODE == BMA_RR)
int uncommon_rr_factorization_recur(long long l)
{
	best_hamm_distance_code = 0x7FFF;
	best_hamm_distance_bit = 0x7FFF;
	
	long long i = 0, j = 0;
	//long long l = 0;
	long long is_root = 0;
	unsigned char root = 0xFF;

#if (1 == DYNAMIC_MEM)
	unsigned char *g_c_q, *g_c_0_y, *g_c_q_origin;
	g_c_q = (unsigned char*)malloc(sizeof(unsigned char) * (term_size_x * term_size_y));
	g_c_0_y = (unsigned char*)malloc(sizeof(unsigned char) * (term_size_x * term_size_y));
	g_c_q_origin = (unsigned char*)malloc(sizeof(unsigned char) * (term_size_x * term_size_y));
#else
	unsigned char g_c_q[term_size_x * term_size_y], g_c_0_y[term_size_x * term_size_y];
#endif

	//for(l = 0; l < pow_val; l++)
	{

		memset(tmp_message, 0xFF, sizeof(unsigned char) * MESSAGE_LEN);
		memcpy(g_c_q_origin, uncommon_term_c_choose[l], sizeof(unsigned char) * (term_size_x * term_size_y));

		for(i = 0; i < GF_FIELD; i++)//test roots
		{
			//DEBUG_INFO("root00: %ld %ld %x\n", 0, i, g_term_c_p[g_term_phase][0][0]);
			memcpy(g_c_q, g_c_q_origin, sizeof(unsigned char) * (term_size_x * term_size_y));
			g_term_0_y_cal_recur(g_c_q, g_c_0_y);

			is_root = chien_searching_for_g_0_y_recur(g_c_0_y, power_polynomial_table[i][0]);
			if(1 == is_root)
			{
				root = power_polynomial_table[i][0];
				tmp_message[0] = root;
				g_term_new_gen_recur(g_c_q, root);

				DEBUG_INFO("root: %ld %ld %x\n", 0, i, root);
				
				uncommon_dfs_rr_recur(g_c_q,
							  g_c_0_y,
							  1,
							  l);
				DEBUG_INFO("root11: %ld %ld %x\n", 0, i, root);
				
				/*is there only one root?*/
				break;
			}
		}

	}

#if (1 == DYNAMIC_MEM)
	free(g_c_q);
	g_c_q = NULL;
	free(g_c_0_y);
	g_c_0_y = NULL;
	free(g_c_q_origin);
	g_c_q_origin = NULL;
#endif

	return 0;
}

int uncommon_dfs_rr_recur(unsigned char *g_c_q,
								  unsigned char *g_c_0_y,
								  long long m,
								  long long l)
{
	long long i = 0, j = 0;

	DEBUG_NOTICE("dfs_rr_recur: %ld\n", m);

	if(MESSAGE_LEN <= m)
	{
		uncommon_check_rr_decoded_result_recur(tmp_message, l);

		return 1;
	}

#if (CFG_RR_MODE == BMA_RR)
	if(SYN_LEN <= m)
	{
		uncommon_check_rr_decoded_result_recur(tmp_message, l);

		return 1;
	}
#endif	

	long long is_root = 0;
	unsigned char root = 0xFF;

#if (1 == DYNAMIC_MEM)
	unsigned char *g_c_q_new;
	g_c_q_new = (unsigned char*)malloc(sizeof(unsigned char) * (term_size_x * term_size_y));
#else
	unsigned char g_c_q_new[term_size_x * term_size_y];
#endif

	for(i = 0; i < GF_FIELD; i++)//test roots
	{
		memcpy(g_c_q_new, g_c_q, sizeof(unsigned char) * (term_size_x * term_size_y));
		g_term_0_y_cal_recur(g_c_q_new, g_c_0_y);

		is_root = chien_searching_for_g_0_y_recur(g_c_0_y, power_polynomial_table[i][0]);
		if(1 == is_root)
		{
			DEBUG_INFO("root0: %ld %ld %x\n", m, i, is_root);
			
			root = power_polynomial_table[i][0];
			tmp_message[m] = root;

			DEBUG_NOTICE("root0.5: %ld %ld %x\n", m, i, root);
			
			g_term_new_gen_recur(g_c_q_new, root);

			DEBUG_INFO("root1: %ld %ld %x\n", m, i, root);

			uncommon_dfs_rr_recur(g_c_q_new,
						  g_c_0_y,
						  m + 1,
						  l);
			DEBUG_INFO("root2: %ld %ld %x\n", 0, i, root);
			
			/*is there only one root?*/
			break;
		}
	}

#if (1 == DYNAMIC_MEM)
	free(g_c_q_new);
	g_c_q_new = NULL;
#endif	

	return 0;
}

int uncommon_check_rr_decoded_result_recur(unsigned char *msg,
														 long long l)
{
	long long i = 0;
	long long hamm_distance_code = 0x7FFF, hamm_distance_bit = 0x7FFF, tmp_code = 0, tmp_bit = 0;
	unsigned char tmp_diff_flag = 0;

	if(0 == l)
	{
		memcpy(first_tmp_message, msg, sizeof(unsigned char) * MESSAGE_LEN);
		tmp_diff_flag = 1;
	}
	else
	{
		
		for(i = 0; i < MESSAGE_LEN; i++)
		{
			if(first_tmp_message[i] != msg[i])
			{
				tmp_diff_flag = 1;
			}
		}
	}

	for(i = 0; i < MESSAGE_LEN; i++)
	{
		DEBUG_NOTICE("msg_to_be_bm: %ld | %ld | %x\n", i, l, msg[i]);
	}

	/*strategy*/
	//if(1 == tmp_diff_flag)
#if (CFG_RR_MODE == BMA_RR)	
	{
		bm_re_encoding(msg, tmp_codeword);
	}
#endif

#if (CFG_RR_MODE == CONV_RE_ENC_SYS)
	unsigned char tmp_cw[CODEWORD_LEN];
	evaluation_encoding_v2(tmp_message, tmp_cw);
	for(i = 0; i < CODEWORD_LEN; i++)
	{
		tmp_codeword[i] = gf_add(tmp_cw[i], phi[i]);
		DEBUG_NOTICE("cw_get: %ld | %x | %x\n",
					 i,
			         tmp_cw[i],
			         tmp_codeword[i]);
	}
#endif

	for(i = 0; i < CODEWORD_LEN; i++)
	{
		DEBUG_NOTICE("tmp_decoded_codeword: %ld %x\n", i, tmp_codeword[i]);
	}
	
	/*this should be checked*/
	memcpy(uncommon_decoded_codeword[l], tmp_codeword, sizeof(unsigned char) * CODEWORD_LEN);

#if 0
	tmp_code = hamm_distance_code_cal(tmp_codeword, received_polynomial, CODEWORD_LEN);
	tmp_bit = hamm_distance_bit_cal(tmp_codeword, received_polynomial, CODEWORD_LEN);

	DEBUG_NOTICE("distance: %d %d | %d %d\n", tmp_code, tmp_bit, best_hamm_distance_code, best_hamm_distance_bit);

	if(tmp_code < best_hamm_distance_code)
	{
		best_hamm_distance_code = tmp_code;
		best_hamm_distance_bit = tmp_bit;
		memcpy(uncommon_decoded_codeword[l], tmp_codeword, sizeof(unsigned char) * CODEWORD_LEN);
#if (1 == SYS_ENC)				
		memcpy(uncommon_decoded_message[l], (tmp_codeword + (CODEWORD_LEN - MESSAGE_LEN)), sizeof(unsigned char) * MESSAGE_LEN);
#else
		memcpy(uncommon_decoded_message[l], msg, sizeof(unsigned char) * MESSAGE_LEN);
#endif
		DEBUG_NOTICE("now best distance: %d %d\n", decoding_ok_flag, best_hamm_distance_code);
	}
	if(tmp_code == best_hamm_distance_code)
	{
		if(tmp_bit < best_hamm_distance_bit)
		{
			best_hamm_distance_bit = tmp_bit;
			memcpy(uncommon_decoded_codeword[l], tmp_codeword, sizeof(unsigned char) * CODEWORD_LEN);
#if (1 == SYS_ENC)				
			memcpy(uncommon_decoded_message[l], (tmp_codeword + (CODEWORD_LEN - MESSAGE_LEN)), sizeof(unsigned char) * MESSAGE_LEN);
#else
			memcpy(uncommon_decoded_message[l], msg, sizeof(unsigned char) * MESSAGE_LEN);
#endif
			DEBUG_NOTICE("distance: %d %d\n", decoding_ok_flag, best_hamm_distance_code);
		}
	}

#if 1//(0 == RE_ENCODING)
	//hamm_distance_debug = hamm_distance_code_cal(msg, message_polynomial, MESSAGE_LEN);
	hamm_distance_debug = hamm_distance_code_cal(tmp_codeword, encoded_polynomial, CODEWORD_LEN);
	DEBUG_NOTICE("Hamming Distance Debug: %ld\n", hamm_distance_debug);

	if(0 == hamm_distance_debug)
	{
		best_hamm_distance_code = 0;
		best_hamm_distance_bit = 0;
		
		memcpy(uncommon_decoded_codeword[l], tmp_codeword, sizeof(unsigned char) * CODEWORD_LEN);
#if (1 == SYS_ENC)				
		memcpy(uncommon_decoded_message[l], (tmp_codeword + (CODEWORD_LEN - MESSAGE_LEN)), sizeof(unsigned char) * MESSAGE_LEN);
#else
		memcpy(uncommon_decoded_message[l], msg, sizeof(unsigned char) * MESSAGE_LEN);
#endif

		if(1 == decoding_ok_flag)
		{
			decoding_ok_flag = 2;
			DEBUG_NOTICE("decoding_ok_flag = 2!\n");
		}
		else
		{
			DEBUG_NOTICE("Strage Err: %d %d\n", decoding_ok_flag, hamm_distance_debug);
		}
		DEBUG_NOTICE("Match!\n");
	}
#endif

#endif

	return 0;
}

int uncommon_recover_codeword(long long l)
{
	long long i = 0, j = 0, cnt = 0;
	//long long l = 0;
	long long best_place = pow_val;
	
	//for(l = 0; l < pow_val; l++)
	{
		for(i = 0; i < CODEWORD_LEN; i++)
		{
			for(j = 0; j < (CODEWORD_LEN - MESSAGE_LEN); j++)
			{
				if(i == unrel_group_seq[j])
				{
					uncommon_decoded_codeword[l][i] = 0xFF;
					cnt++;
				}
			}

			if(cnt >= (CODEWORD_LEN - MESSAGE_LEN))
			{
				break;
			}
		}

		for(i = 0; i < CODEWORD_LEN; i++)
		{
			DEBUG_NOTICE("decoded_codeword: %x\n", uncommon_decoded_codeword[l][i]);
		}
		erasure_decoding(uncommon_decoded_codeword[l], unrel_group_seq);
		//erasure_decoding_lag(uncommon_decoded_codeword[l]);
		memcpy(uncommon_decoded_codeword[l], phi, sizeof(unsigned char) * CODEWORD_LEN);
		memcpy(uncommon_decoded_message[l], uncommon_decoded_codeword[l] + (CODEWORD_LEN - MESSAGE_LEN), sizeof(unsigned char) * MESSAGE_LEN);
	}

#if 0
	best_place = uncommon_check_decoded_result();
	memcpy(decoded_codeword, uncommon_decoded_codeword[best_place], sizeof(unsigned char) * CODEWORD_LEN);
	memcpy(decoded_message, decoded_codeword + (CODEWORD_LEN - MESSAGE_LEN), sizeof(unsigned char) * MESSAGE_LEN);

	for(i = 0; i < MESSAGE_LEN; i++)
	{
		DEBUG_IMPOTANT("uncommon_decoded_message: %d | %d | %x\n",
		               best_place,
		               i,
		               decoded_message[i]);
	}
	if(0 != best_place)
	{
		DEBUG_SYS("Best Place: %ld\n", best_place);
	}
#endif	
	
	return 0;
}
#endif

int uncommon_interpolation_exit()
{
	long long i = 0, j = 0, k = 0;

	for(i = 0; i < YITA; i++)
	{
		free(uncommon_seq[i]);
		uncommon_seq[i] = NULL;
	}
	free(uncommon_seq);

#if (0 == CFG_BR)
	for(i = 0; i < d_y_num; i++)
	{
		free(common_term_c_p[i]);
		common_term_c_p[i] = NULL;
	}
	free(common_term_c_p);

	for (i = 0; i < pow_val; i++)
	{
		for(j = 0; j < d_y_num; j++)
		{
			free(uncommon_term_c_p[i][j]);
			uncommon_term_c_p[i][j] = NULL;;
		}

		free(uncommon_term_c_p[i]);
		uncommon_term_c_p[i] = NULL;
	}
	free(uncommon_term_c_p);
	uncommon_term_c_p = NULL;

	for (i = 0; i < pow_val; i++)
	{
		for(j = 0; j < d_y_num; j++)
		{
			free(uncommon_table_c_prev[i][j]);
			uncommon_table_c_prev[i][j] = NULL;;
		}

		free(uncommon_table_c_prev[i]);
		uncommon_table_c_prev[i] = NULL;
	}
	free(uncommon_table_c_prev);
	uncommon_table_c_prev = NULL;

	for(i = 0; i < pow_val; i++)
	{
		free(uncommon_weight_pol[i]);
		uncommon_weight_pol[i] = NULL;
	}
	free(uncommon_weight_pol);
	for(i = 0; i < pow_val; i++)
	{
		free(uncommon_weight_pol_1_k_1[i]);
		uncommon_weight_pol_1_k_1[i] = NULL;
	}
	free(uncommon_weight_pol_1_k_1);
	for(i = 0; i < pow_val; i++)
	{
		free(uncommon_lexorder_pol[i]);
		uncommon_lexorder_pol[i] = NULL;
	}
	free(uncommon_lexorder_pol);

	free(common_term_weight_pol);
	common_term_weight_pol = NULL;
	free(common_term_weight_pol_1_k_1);
	common_term_weight_pol_1_k_1 = NULL;
	free(common_term_lexorder_pol);
	common_term_lexorder_pol = NULL;
	
	free(uncommon_l_s);
	uncommon_l_s = NULL;
	free(uncommon_l_o);
	uncommon_l_o = NULL;
	free(uncommon_l_w);
	uncommon_l_w = NULL;
#endif

	for(i = 0; i < pow_val; i++)
	{
		free(uncommon_term_c_choose[i]);
		uncommon_term_c_choose[i] = NULL;
	}
	free(uncommon_term_c_choose);
	
	for(i = 0; i < pow_val; i++)
	{
		free(uncommon_decoded_codeword[i]);
		uncommon_decoded_codeword[i] = NULL;
		free(uncommon_decoded_message[i]);
		uncommon_decoded_message[i] = NULL;
		free(tst_vct[i]);
		tst_vct[i] = NULL;
	}
	free(uncommon_decoded_codeword);
	uncommon_decoded_codeword = NULL;
	free(uncommon_decoded_message);
	uncommon_decoded_message = NULL;
	free(tst_vct);
	tst_vct = NULL;

#if (1 == CFG_BR)	
	free(tst_vct_cmm);
	tst_vct_cmm = NULL;
#endif

	DEBUG_INFO("%s\n", __func__);
#if (1 == CFG_ADAPTIVE_PARALLEL)
	for(i = 0; i < pow_val; i++)
	{
		free(tst_vct_seq[i]);
		tst_vct_seq[i] = NULL;
	}
	free(tst_vct_seq);
	tst_vct_seq = NULL;
#else
	for(i = 0; i < PARALLEL_BATCH_NUM; i++)
	{
		free(tst_vct_seq[i]);
		tst_vct_seq[i] = NULL;
	}
	free(tst_vct_seq);
	tst_vct_seq = NULL;
#endif	

	free(decoded_tst_vct_seq);
	decoded_tst_vct_seq = NULL;

#if (1 == CFG_STORE_PARALEL)
	long long sort_len = (long long)pow(2, CFG_STORE_LEN);
	long long store_size = pow_val / sort_len;
	for (i = 0; i < store_size; i++)
	{
		for(j = 0; j < d_y_num; j++)
		{
			free(store_uncommon_table_c_prev[i][j]);
			store_uncommon_table_c_prev[i][j] = NULL;;
		}

		free(store_uncommon_table_c_prev[i]);
		store_uncommon_table_c_prev[i] = NULL;
	}
	free(store_uncommon_table_c_prev);
	store_uncommon_table_c_prev = NULL;

	free(store_flag);
	store_flag = NULL;

	for(i = 0; i < store_size; i++)
	{
		free(store_group[i]);
		store_group[i] = NULL;
	}
	free(store_group);
	store_group = NULL;
#endif

	free(tst_vct_rel);
	tst_vct_rel= NULL;

#if (1 == CFG_IMD_STORE)
	for(i = 0; i < YITA; i++)
	{
		for(j = 0; j < pow_val; j++)
		{
			for(k = 0; k < d_y_num; k++)
			{
				free(store_q_c_prev[i][j][k]);
				store_q_c_prev[i][j][k] = NULL;;
			}

			free(store_q_c_prev[i][j]);
			store_q_c_prev[i][j] = NULL;
		}
		
		free(store_q_c_prev[i]);
		store_q_c_prev[i] = NULL;
		
		free(store_q_c_flag[i]);
		store_q_c_flag[i] = NULL;
	}
	free(store_q_c_prev);
	store_q_c_prev = NULL;
	free(store_q_c_flag);
	store_q_c_flag = NULL;
#endif	

	free(adaptive_vct_seq);
	adaptive_vct_seq = NULL;
	free(adaptive_vct_seq_mark);
	adaptive_vct_seq_mark = NULL;

	return 0;
}

int fast_check_tst_vct_radius(long long dcd_cwd_idx, long long tst_vct_idx)
{
	long long i = 0;
	int cwd_diff_cnt = 0;

	DEBUG_INFO("fast_check_tst_vct_radius: %d %d\n", dcd_cwd_idx, tst_vct_idx);

	for(i = 0; i < CODEWORD_LEN; i++)
	{	
		if(uncommon_decoded_codeword[dcd_cwd_idx][i]
		   != tst_vct[tst_vct_idx][i])
		{
			cwd_diff_cnt++;
		}	
	}

	return cwd_diff_cnt;
}

int fast_skip_tst_vct(long long l, long long dcd_num)
{
	long long i = 0;
	int tst_skip_cnt = CODEWORD_LEN;

	for(i = 0; i < dcd_num; i++)
	{
		tst_skip_cnt = fast_check_tst_vct_radius(decoded_tst_vct_seq[i], l);
		DEBUG_INFO("tst_skip_cnt: %d %d %d %d\n", decoded_tst_vct_seq[i], l, dcd_num, tst_skip_cnt);
		if(((CODEWORD_LEN - MESSAGE_LEN) / 2) >= tst_skip_cnt)
		{
			memcpy(uncommon_decoded_codeword[l],
			       uncommon_decoded_codeword[decoded_tst_vct_seq[i]],
			       sizeof(unsigned char) * CODEWORD_LEN);
			memcpy(uncommon_decoded_message[l],
			       uncommon_decoded_message[decoded_tst_vct_seq[i]],
			       sizeof(unsigned char) * MESSAGE_LEN);
			break;
		}
	}

	return tst_skip_cnt;
}

#endif

int tst_vct_seq_cal()
{
	long long i = 0, j = 0, k = 0;
	long long batch_size = pow_val / PARALLEL_BATCH_NUM;
#if 0
	for(i = 0; i < PARALLEL_BATCH_NUM; i++)
	{
		for(j = 0; j < batch_size; j++)
		{
			tst_vct_seq[i][j] = j * PARALLEL_BATCH_NUM + i;
			//DEBUG_SYS("tst_vct_seq: %ld %ld | %ld\n", i, j, tst_vct_seq[i][j]);
		}
	}
#endif
#if 1
	for(i = 0; i < PARALLEL_BATCH_NUM; i++)
	{
		for(j = 0; j < batch_size; j++)
		{
			tst_vct_seq[i][j] = i * batch_size + j;
		}
	}
#endif	
#if 0
	for(i = 0; i < PARALLEL_BATCH_NUM; i++)
	{
		for(j = 0; j < batch_size; j++)
		{
			tst_vct_seq[i][j] = chnl_rel_order_idx[j * PARALLEL_BATCH_NUM + i];
		}
	}
#endif
#if 0
	for(i = 0; i < PARALLEL_BATCH_NUM; i++)
	{
		for(j = 0; j < batch_size; j++)
		{
			tst_vct_seq[i][j] = chnl_rel_order_idx[i * batch_size + j];
		}
	}
#endif

	long long all_seq[pow_val];
	float all_chnl_rel[pow_val];
	for(i = 0; i < pow_val; i++)
	{
		all_seq[i] = i;
	}
	memcpy(all_chnl_rel, tst_vct_rel, sizeof(float) * pow_val);
	BubbleSort5(all_chnl_rel, pow_val, all_seq);
	for(i = 0; i < pow_val; i++)
	{
		DEBUG_INFO("all_rel_sort: %ld | %f | %ld\n",
		           i,
		           all_chnl_rel[i],
		           all_seq[i]);
	}
	memcpy(adaptive_vct_seq, all_seq, sizeof(long long) * pow_val);

#if (1 == CFG_STORE_PARALEL)
	long long sort_start_idx = 0, sort_len = (long long)pow(2, CFG_STORE_LEN);
	long long sort_seq[sort_len];
	float sort_chnl_rel[sort_len];
	
	DEBUG_INFO("store: %ld %ld %ld %ld\n",
	          sort_len,
	          pow_val / sort_len,
	          store_cnt - store_cnt_prev,
	          store_cnt);
	store_cnt_prev = store_cnt;
	for(i = 0; i < (pow_val / sort_len); i++)
	{
		sort_start_idx = i * sort_len;
		for(j = 0; j < sort_len; j++)
		{
			sort_seq[j] = sort_start_idx + j;
			sort_chnl_rel[j] = tst_vct_rel[sort_seq[j]];
		}
		BubbleSort5(sort_chnl_rel, sort_len, sort_seq);
		for(j = 0; j < sort_len; j++)
		{
			all_seq[sort_start_idx + j] = sort_seq[j];
			DEBUG_INFO("store_sort: %ld %ld | %f | %ld\n",
			           i,
			           j,
			           sort_chnl_rel[j],
			           sort_seq[j]);
			store_group[i][j] = sort_seq[j];           
		}
	}
#endif	

#if (1 == CFG_GROUP_SCHEME)
#if 0
	for(i = 0; i < PARALLEL_BATCH_NUM; i++)
	{
		for(j = 0; j < batch_size; j++)
		{
			tst_vct_seq[i][j] = all_seq[i * batch_size + j];
			DEBUG_INFO("tst_vct_seq: %ld %ld | %ld\n",
			           i,
			           j,
			           tst_vct_seq[i][j]);
		}
	}
#endif
	k = 0;
	for(j = 0; j < batch_size; j++)
	{
		for(i = 0; i < PARALLEL_BATCH_NUM; i++)
		{
			tst_vct_seq[i][j] = all_seq[k];
			k++;
			DEBUG_INFO("tst_vct_seq: %ld %ld | %ld\n",
			           i,
			           j,
			           tst_vct_seq[i][j]);
		}
	}
#endif

#if (2 == CFG_GROUP_SCHEME)
	unsigned char seq_mark[pow_val];
	memset(seq_mark, 0, sizeof(unsigned char) * pow_val);
	unsigned char batch_side = 0;
	long long d_vct = 0;
	
	for(i = 0; i < PARALLEL_BATCH_NUM; i++)
	{
		if((PARALLEL_BATCH_NUM / 2) > i)
		{
			batch_side = 0;
		}
		else
		{
			batch_side = 1;
		}

		if(0 == batch_side)
		{
			tst_vct_seq[i][0] = i * batch_size;
		}
		else
		{
			tst_vct_seq[i][0] = i * batch_size + (batch_size - 1);
		}
		seq_mark[tst_vct_seq[i][0]] = 1;

		for(j = 1; j < batch_size; j++)
		{
			if(0 == batch_side)
			{
				for(k = 0; k < pow_val; k++)
				{
					d_vct = hamm_distance_code_cal(tst_vct[tst_vct_seq[i][j - 1]],
					                               tst_vct[k],
					                               CODEWORD_LEN);
					if((1 == d_vct)
					   && (0 == seq_mark[k]))
					{
						tst_vct_seq[i][j] = k;
						seq_mark[tst_vct_seq[i][j]] = 1;
						break;
					}
				}
			}
			else
			{
				for(k = pow_val - 1; k >= 0; k--)
				{
					d_vct = hamm_distance_code_cal(tst_vct[tst_vct_seq[i][j - 1]],
					                               tst_vct[k],
					                               CODEWORD_LEN);
					if((1 == d_vct)
					   && (0 == seq_mark[k]))
					{
						tst_vct_seq[i][j] = k;
						seq_mark[tst_vct_seq[i][j]] = 1;
						break;
					}
				}
			}

			DEBUG_INFO("tst_vct_seq: %ld %ld | %ld\n",
			           i,
			           j,
			           tst_vct_seq[i][j]);
		}
	}
#endif

#if (3 == CFG_GROUP_SCHEME)
	unsigned char seq_mark[pow_val];
	memset(seq_mark, 0, sizeof(unsigned char) * pow_val);
	unsigned char batch_side = 0;

	for(i = 0; i < PARALLEL_BATCH_NUM; i++)
	{
		if((PARALLEL_BATCH_NUM / 2) > i)
		{
			batch_side = 0;
		}
		else
		{
			batch_side = 1;
		}

		if(0 == batch_side)
		{
			tst_vct_seq[i][0] = i * batch_size;
		}
		else
		{
			tst_vct_seq[i][0] = i * batch_size + (batch_size - 1);
		}
		seq_mark[tst_vct_seq[i][0]] = 1;

		for(j = 1; j < batch_size; j++)
		{
			if(0 == batch_side)
			{
				tst_vct_seq[i][j] = all_seq[i * batch_size + j];
				seq_mark[tst_vct_seq[i][j]] = 1;
			}
			else
			{
				tst_vct_seq[i][j] = all_seq[i * batch_size + j - 1];
				seq_mark[tst_vct_seq[i][j]] = 1;
			}

			DEBUG_INFO("tst_vct_seq: %ld %ld | %ld\n",
			           i,
			           j,
			           tst_vct_seq[i][j]);
		}
	}
#endif

#if (4 == CFG_GROUP_SCHEME)
	k = 0;
	unsigned char seq_mark[pow_val];
	memset(seq_mark, 0, sizeof(unsigned char) * pow_val);

	for(i = 0; i < PARALLEL_BATCH_NUM; i++)
	{
		if(0 == i)
		{
			tst_vct_seq[i][0] = 0;
		}
		else if((PARALLEL_BATCH_NUM - 1) == i)
		{
			tst_vct_seq[i][0] = pow_val - 1;
		}
		else
		{
			tst_vct_seq[i][0] = i * batch_size + batch_size / 2;
		}
		seq_mark[tst_vct_seq[i][0]] = 1;

		for(j = 1; j < batch_size; j++)
		{
			for(k = 0; k < batch_size; k++)
			{
				if(0 == seq_mark[all_seq[i * batch_size + k]])
				{
					tst_vct_seq[i][j] = all_seq[i * batch_size + k];
					seq_mark[tst_vct_seq[i][j]] = 1;
					break;
				}
			}
			DEBUG_INFO("tst_vct_seq: %ld %ld | %ld\n",
			           i,
			           j,
			           tst_vct_seq[i][j]);
		}
	}
#endif

#if (5 == CFG_GROUP_SCHEME)
	for(i = 0; i < PARALLEL_BATCH_NUM; i++)
	{
		for(j = 0; j < batch_size; j++)
		{
			tst_vct_seq[i][j] = j * PARALLEL_BATCH_NUM + i;
			DEBUG_INFO("tst_vct_seq: %ld %ld | %ld\n",
			           i,
			           j,
			           tst_vct_seq[i][j]);
		}
	}
#endif

#if (6 == CFG_GROUP_SCHEME)
	/*pow_val should be larger than 4.*/
	long long tmp = 0;
	for(i = 0; i < pow_val; i++)
	{
		for(j = 0; j < pow_val; j++)
		{
			if(0 == all_seq[j])
			{
				tmp = all_seq[0];
				all_seq[0] = all_seq[j];
				all_seq[j] = tmp;
			}
			if(1 == all_seq[j])
			{
				tmp = all_seq[1];
				all_seq[1] = all_seq[j];
				all_seq[j] = tmp;
			}
			if((pow_val - 1) == all_seq[j])
			{
				tmp = all_seq[2];
				all_seq[2] = all_seq[j];
				all_seq[j] = tmp;
			}
			if(((pow_val + 1) / 2 + 1) == all_seq[j])
			{
				tmp = all_seq[3];
				all_seq[3] = all_seq[j];
				all_seq[j] = tmp;
			}
		}
	}

	for(i = 0; i < PARALLEL_BATCH_NUM; i++)
	{
		for(j = 0; j < batch_size; j++)
		{
			tst_vct_seq[i][j] = all_seq[j * PARALLEL_BATCH_NUM + i];
			DEBUG_INFO("tst_vct_seq: %ld %ld | %ld\n",
			           i,
			           j,
			           tst_vct_seq[i][j]);
		}
	}
#endif

#if (7 == CFG_GROUP_SCHEME)
	long long s[PARALLEL_BATCH_NUM];
	unsigned char seq_mark[pow_val];
	memset(seq_mark, 0, sizeof(unsigned char) * pow_val);
	
	for(i = 0; i < PARALLEL_BATCH_NUM; i++)
	{
		s[i] = (pow_val - 1) / (PARALLEL_BATCH_NUM - 1) * i;
		tst_vct_seq[i][0] = s[i];
		seq_mark[tst_vct_seq[i][0]] = 1;
		DEBUG_INFO("tst_vct_seq: %ld %ld | %ld\n",
		           i,
		           0,
		           tst_vct_seq[i][0]);
	}
	k = 0;
	long long l = 0;
	for(j = 1; j < batch_size; j++)
	{
		for(i = 0; i < PARALLEL_BATCH_NUM; i++)
		{
			while(1 == seq_mark[all_seq[k]])
			{
				k++;
			}
			tst_vct_seq[i][j] = all_seq[k];
			k++;
			DEBUG_INFO("tst_vct_seq: %ld %ld | %ld\n",
			           i,
			           j,
			           tst_vct_seq[i][j]);
		}
	}
#endif

#if (8 == CFG_GROUP_SCHEME)
	long long tst_vct_cnt = 0;
	for(j = 0; j < batch_size; j++)
	{
		for(i = 0; i < PARALLEL_BATCH_NUM; i++)
		{
			tst_vct_seq[i][j] = pow_val - 1 - tst_vct_cnt;
			DEBUG_INFO("tst_vct_seq: %ld %ld | %ld\n",
			           i,
			           j,
			           tst_vct_seq[i][j]);
			tst_vct_cnt++;           
		}
	}
#endif

	return 0;
}

int phi_compare_fast_skip(long long tvt_idx)
{
	long long i = 0;
	long long diff_cnt = 0;
	
	if(pow_val <= tvt_idx)
	{
		return 0;
	}
	
	for(i = 0; i < CODEWORD_LEN; i++)
	{
		if(phi[i] != tst_vct[tvt_idx][i])
		{
			diff_cnt++;
		}
	}
	if(((CODEWORD_LEN - MESSAGE_LEN) / 2) >= diff_cnt)
	{
		DEBUG_INFO("diff_cnt: %ld\n", diff_cnt);
		return 1;
	}

	return 0;
}

int rearrange_tst_vct_old(long long tst_vct_proc_num, long long round_idx)
{
	long long i = 0, j =0;
	int tst_skip_cnt = CODEWORD_LEN;
	long long batch_size = pow_val / PARALLEL_BATCH_NUM;
	long long round_size = PARALLEL_BATCH_NUM;
	long long vct_cnt = tst_vct_proc_num;
	
	if(pow_val <= vct_cnt)
	{
		//DEBUG_SYS("vct_cnt_err: %ld\n", vct_cnt);
	}

	for(i = tst_vct_proc_num; i < pow_val; i++)
	{
		tst_skip_cnt = fast_skip_tst_vct(adaptive_vct_seq[i], tst_vct_proc_num);
		
#if (1 == CFG_PHI_FAST_SKIP)		
		if(1 == phi_compare_fast_skip(adaptive_vct_seq[i]))
		{
			tst_skip_cnt = ((CODEWORD_LEN - MESSAGE_LEN) / 2);
		}
#endif
		if((((CODEWORD_LEN - MESSAGE_LEN) / 2) >= tst_skip_cnt)
			&& (0 == adaptive_vct_seq_mark[adaptive_vct_seq[i]]))
		{
			adaptive_vct_seq_mark[adaptive_vct_seq[i]] = 1;
			processed_tst_vct_num++;
		}
		DEBUG_INFO("adaptive_vct_seq_mark: %ld %ld | %ld | %d\n",
				   tst_vct_proc_num,
				   i,
				   adaptive_vct_seq[i],
				   adaptive_vct_seq_mark[adaptive_vct_seq[i]]);
	}

#if (1 == CFG_ADAPTIVE_PARALLEL)
	for(i = round_idx; i < pow_val; i++)
	{
		for(j = 0; j < pow_val; j++)
		{
			//DEBUG_INFO("%s: %ld %ld\n", __func__, i, j);
		
			if(j >= adaptive_batch_num[i])
			{
				tst_vct_seq[j][i] = -1;
				continue;
			}
		
			if(vct_cnt >= pow_val)
			{
				tst_vct_seq[j][i] = -1;
				continue;
			}

			while((1 == adaptive_vct_seq_mark[adaptive_vct_seq[vct_cnt]])
				  && (vct_cnt < pow_val))
			{
				vct_cnt++;
				if(vct_cnt >= pow_val)
				{
					DEBUG_INFO("while in %s: %ld\n", __func__, vct_cnt);
					break;
				}
			}
			
			if(vct_cnt >= pow_val)
			{
				tst_vct_seq[j][i] = -1;
				continue;
			}

			tst_vct_seq[j][i] = adaptive_vct_seq[vct_cnt];
			
			DEBUG_INFO("rearrange_tst_vct: %ld | %ld %ld | %ld %ld | %ld %ld %d | %ld\n",
					   round_idx,
					   tst_vct_proc_num,
					   processed_tst_vct_num,
					   i,
					   j,
					   vct_cnt,
					   adaptive_vct_seq[vct_cnt],
					   adaptive_vct_seq_mark[adaptive_vct_seq[vct_cnt]],
					   tst_vct_seq[j][i]);

			vct_cnt++;		   
		}
	}
#else
	for(i = round_idx; i < batch_size; i++)
	{
		for(j = 0; j < round_size; j++)
		{
			DEBUG_INFO("%s: %ld %ld\n", __func__, i, j);
		
			if(vct_cnt >= pow_val)
			{
				tst_vct_seq[j][i] = -1;
				continue;
			}

			while((1 == adaptive_vct_seq_mark[adaptive_vct_seq[vct_cnt]])
				  && (vct_cnt < pow_val))
			{
				vct_cnt++;
				if(vct_cnt >= pow_val)
				{
					DEBUG_INFO("while in %s: %ld\n", __func__, vct_cnt);
					break;
				}
			}
			
			if(vct_cnt >= pow_val)
			{
				tst_vct_seq[j][i] = -1;
				continue;
			}

			tst_vct_seq[j][i] = adaptive_vct_seq[vct_cnt];
			
			DEBUG_INFO("rearrange_tst_vct: %ld | %ld %ld | %ld %ld | %ld %ld %d | %ld\n",
					   round_idx,
					   tst_vct_proc_num,
					   processed_tst_vct_num,
					   i,
					   j,
					   vct_cnt,
					   adaptive_vct_seq[vct_cnt],
					   adaptive_vct_seq_mark[adaptive_vct_seq[vct_cnt]],
					   tst_vct_seq[j][i]);

			vct_cnt++;		   
		}
	}
#endif
	DEBUG_INFO("%s\n", __func__);

	return 0;
}

int rearrange_tst_vct(long long tst_vct_proc_num, long long round_idx)
{
	long long i = 0, j =0;
	int tst_skip_cnt = CODEWORD_LEN;
	long long batch_size = pow_val / PARALLEL_BATCH_NUM;
	long long round_size = PARALLEL_BATCH_NUM;
	long long vct_cnt = tst_vct_proc_num;
	
	if(pow_val <= vct_cnt)
	{
		//DEBUG_SYS("vct_cnt_err: %ld\n", vct_cnt);
	}

	//for(i = tst_vct_proc_num; i < pow_val; i++)
	for(i = 0; i < pow_val; i++)
	{
		if(0 != adaptive_vct_seq_mark[adaptive_vct_seq[i]])
		{
			continue;
		}	

		tst_skip_cnt = fast_skip_tst_vct(adaptive_vct_seq[i], tst_vct_proc_num);

#if (1 == CFG_PHI_FAST_SKIP)		
		if(1 == phi_compare_fast_skip(adaptive_vct_seq[i]))
		{
			tst_skip_cnt = ((CODEWORD_LEN - MESSAGE_LEN) / 2);
		}
#endif		
		
		if((((CODEWORD_LEN - MESSAGE_LEN) / 2) >= tst_skip_cnt)
			&& (0 == adaptive_vct_seq_mark[adaptive_vct_seq[i]]))
		{
			adaptive_vct_seq_mark[adaptive_vct_seq[i]] = 1;
#if (0 == CFG_NEW_TST_VCT)			
			processed_tst_vct_num++;
			DEBUG_INFO("processed_tst_vct_skip: %ld %ld\n", processed_tst_vct_num, adaptive_vct_seq[i]);
#endif		
		}
		DEBUG_INFO("adaptive_vct_seq_mark: %ld %ld | %ld | %d | %ld\n",
				   tst_vct_proc_num,
				   i,
				   adaptive_vct_seq[i],
				   adaptive_vct_seq_mark[adaptive_vct_seq[i]],
				   processed_tst_vct_num);
	}

#if 1//(0 == CFG_NEW_TST_VCT)
	vct_cnt = 0;
#endif

#if (1 == CFG_ADAPTIVE_PARALLEL)
	for(i = round_idx; i < pow_val; i++)
	{
		for(j = 0; j < pow_val; j++)
		{
			if(j >= adaptive_batch_num[i])
			{
				tst_vct_seq[j][i] = -1;
				continue;
			}
		
			//if(vct_cnt >= pow_val)
			if(processed_tst_vct_num >= pow_val)
			{
				tst_vct_seq[j][i] = -1;
				continue;
			}
			
			if(vct_cnt >= pow_val)
			{
				tst_vct_seq[j][i] = -1;
				continue;
			}

#if (0 == CFG_NEW_TST_VCT)
			while((0 != adaptive_vct_seq_mark[adaptive_vct_seq[vct_cnt]])
				  && (vct_cnt < pow_val))
			{
				vct_cnt++;
				if(vct_cnt >= pow_val)
				{
					DEBUG_INFO("while in %s: %ld\n", __func__, vct_cnt);
					break;
				}
			}			
#else
			while((0 != adaptive_vct_seq_mark[adaptive_vct_seq[vct_cnt]])
				  && (vct_cnt < pow_val))
			{
				vct_cnt++;
				if(vct_cnt >= pow_val)
				{
					DEBUG_INFO("while in %s: %ld\n", __func__, vct_cnt);
					break;
				}
				
				if((1 == adaptive_vct_seq_mark[adaptive_vct_seq[vct_cnt]])
					&& (vct_cnt < pow_val)
				  	&& (new_tst_vct_cnt < pow_val)
				  	&& (0 == new_tst_vct_mark[adaptive_vct_seq[vct_cnt]]))
				{
					memcpy(tst_vct[adaptive_vct_seq[vct_cnt]], new_tst_vct[new_tst_vct_cnt], sizeof(unsigned char) * CODEWORD_LEN);
					memcpy(tst_vct_trans[adaptive_vct_seq[vct_cnt]], new_tst_vct_trans[new_tst_vct_cnt], sizeof(unsigned char) * CODEWORD_LEN);
					DEBUG_INFO("replace %ld by %ld\n", adaptive_vct_seq[vct_cnt], new_tst_vct_cnt);
					new_tst_vct_mark[adaptive_vct_seq[vct_cnt]] = 1;
					new_tst_vct_cnt++;

					replace_cnt++;

#if 0					
					tst_skip_cnt = fast_skip_tst_vct(adaptive_vct_seq[vct_cnt], tst_vct_proc_num);
					if(((CODEWORD_LEN - MESSAGE_LEN) / 2) >= tst_skip_cnt)
					{
						//replace_cnt++;
						DEBUG_INFO("useless new tst vct: old-%ld | new-%ld\n", adaptive_vct_seq[vct_cnt], new_tst_vct_cnt - 1);
					}
#endif
					break;
				}
				
				if(vct_cnt >= pow_val)
				{
					DEBUG_INFO("while in %s: %ld\n", __func__, vct_cnt);
					break;
				}
			}
#endif
			
			if(vct_cnt >= pow_val)
			{
				tst_vct_seq[j][i] = -1;
				continue;
			}

			tst_vct_seq[j][i] = adaptive_vct_seq[vct_cnt];
			
			DEBUG_INFO("rearrange_tst_vct: %ld | %ld %ld | %ld %ld | %ld %ld %d | %ld\n",
					   round_idx,
					   tst_vct_proc_num,
					   processed_tst_vct_num,
					   i,
					   j,
					   vct_cnt,
					   adaptive_vct_seq[vct_cnt],
					   adaptive_vct_seq_mark[adaptive_vct_seq[vct_cnt]],
					   tst_vct_seq[j][i]);

			vct_cnt++;		   
		}
	}
#else
	for(i = round_idx; i < batch_size; i++)
	{
		for(j = 0; j < round_size; j++)
		{
			DEBUG_INFO("%s: %ld %ld\n", __func__, i, j);
		
			if(vct_cnt >= pow_val)
			{
				tst_vct_seq[j][i] = -1;
				continue;
			}

			while((1 == adaptive_vct_seq_mark[adaptive_vct_seq[vct_cnt]])
				  && (vct_cnt < pow_val))
			{
				vct_cnt++;
				if(vct_cnt >= pow_val)
				{
					DEBUG_INFO("while in %s: %ld\n", __func__, vct_cnt);
					break;
				}
			}
			
			if(vct_cnt >= pow_val)
			{
				tst_vct_seq[j][i] = -1;
				continue;
			}

			tst_vct_seq[j][i] = adaptive_vct_seq[vct_cnt];
			
			DEBUG_INFO("rearrange_tst_vct: %ld | %ld %ld | %ld %ld | %ld %ld %d | %ld\n",
					   round_idx,
					   tst_vct_proc_num,
					   processed_tst_vct_num,
					   i,
					   j,
					   vct_cnt,
					   adaptive_vct_seq[vct_cnt],
					   adaptive_vct_seq_mark[adaptive_vct_seq[vct_cnt]],
					   tst_vct_seq[j][i]);

			vct_cnt++;		   
		}
	}
#endif
	DEBUG_INFO("%s\n", __func__);

	return 0;
}

#if (1 == CFG_PRG_DECODING)
int MLcriterion(unsigned char est_cwd[])
{
    long long i, j;
    float gama1, gama2;
    unsigned char same_pos_vector[CODEWORD_LEN], differ_pos_vector[CODEWORD_LEN];
    long long count1 = 0, count2 = 0;
    long long Hammin_dis, differ_pos, same_pos;
    float symbol_reliabilty_metric[CODEWORD_LEN];
    float temp, temp_metric[CODEWORD_LEN];
    float max_symbol_reliability, sec_max_symbol_reliability;
    long long max_row, sec_max_row;
    unsigned char cwd[CODEWORD_LEN];

    for (i = 0; i < CODEWORD_LEN; i++)
    {
        same_pos_vector[i] = 0xFF;
        differ_pos_vector[i] = 0xFF;
        temp_metric[i] = 0;
        cwd[i] = est_cwd[i];
    }

    for (i = 0; i < CODEWORD_LEN; i++)
    {
        if (cwd[i] == received_polynomial[i])
        {
            same_pos_vector[count1] = i;
            count1++;
        }
        else
        {
            differ_pos_vector[count2] = i;
            count2++;
        }
    }
    Hammin_dis = count2;
    gama1 = 1;
    for (j = 0; j < count2; j++)
    {
        differ_pos = differ_pos_vector[j];
        max_symbol_reliability = 0;
        for (i = 0; i < GF_FIELD; i++)
        {
            if (chnl_rel_matrix[i][differ_pos] > max_symbol_reliability)
                max_symbol_reliability = chnl_rel_matrix[i][differ_pos];
        }
        for (i = 0; i < GF_FIELD; i++)
        {
            if (power_polynomial_table[i][0] == cwd[differ_pos])
            {
                //temp=i;
                break;
            }
        }
        DEBUG_INFO("gama1: %d %d | %f %f %f\n",
        		   differ_pos,
        		   i,
	    		   gama1,
	    		   max_symbol_reliability,
	    		   chnl_rel_matrix[i][differ_pos]);
        gama1 = gama1 * max_symbol_reliability / chnl_rel_matrix[i][differ_pos];
    }
    for (i = 0; i < count1; i++)
    {
        same_pos = same_pos_vector[i];
        max_symbol_reliability = 0;
        sec_max_symbol_reliability = 0;
        max_row = -1;
        sec_max_row = -1;
        for (j = 0; j < GF_FIELD; j++)
        {
            if (chnl_rel_matrix[j][same_pos] > max_symbol_reliability)
            {
                sec_max_symbol_reliability = max_symbol_reliability;
                sec_max_row = max_row;
                max_symbol_reliability = chnl_rel_matrix[j][same_pos];
                max_row = j;
            }
            else if (chnl_rel_matrix[j][same_pos] > sec_max_symbol_reliability)
            {
                sec_max_symbol_reliability = chnl_rel_matrix[j][same_pos];
                sec_max_row = j;
            }
        }
        symbol_reliabilty_metric[i] = max_symbol_reliability / sec_max_symbol_reliability;
        temp_metric[i] = symbol_reliabilty_metric[i];
    }
    //insertion sort the metric from small to big
    for (j = 1; j < count1; j++)
    {
        temp = temp_metric[j];
        i = j - 1;
        while (i >= 0 && temp_metric[i] > temp)
        {
            temp_metric[i + 1] = temp_metric[i];
            i = i - 1;
        }
        temp_metric[i + 1] = temp;
    }
    gama2 = 1;
    for (i = 0; i < (CODEWORD_LEN - MESSAGE_LEN + 1 - Hammin_dis); i++)
    {
        gama2 = gama2 * temp_metric[i];
    }
    DEBUG_INFO("gama: %f %f\n",
    		   gama1,
    		   gama2);
    if (gama1 <= gama2)
        return 1;
    else
        return 0;
}
#endif

int check_lcc_result()
{
	long long i = 0, j = 0;
	long long best_place = pow_val;
	long long right_compare_cnt = 0, element_idx = 0;

	best_place = uncommon_check_decoded_result();
	memcpy(decoded_codeword, uncommon_decoded_codeword[best_place], sizeof(unsigned char) * CODEWORD_LEN);
	memcpy(decoded_message, decoded_codeword + (CODEWORD_LEN - MESSAGE_LEN), sizeof(unsigned char) * MESSAGE_LEN);

	for(i = 0; i < MESSAGE_LEN; i++)
	{
		DEBUG_IMPOTANT("uncommon_decoded_message: %d | %d | %x\n",
		               best_place,
		               i,
		               decoded_message[i]);
	}
	if(0 != best_place)
	{
		DEBUG_IMPOTANT("Best Place: %ld\n", best_place);
	}

#if (1 == CFG_NEW_TST_VCT)
	unsigned char right_flag = 1;

	for(i = 0; i < MESSAGE_LEN; i++)
	{
		if(decoded_message[i] != message_polynomial[i])
		{
			right_flag = 0;
			break;
		}
	}
	if((1 == right_flag) && (1 == new_tst_vct_mark[best_place]))
	{
		DEBUG_SYS("new_tst_vct_right: %ld | %d\n", best_place, new_tst_vct_mark[best_place]);
		new_tst_vct_ok_cnt++;
	}
	
	symbol_err_cnt = 0;
	thr_cnt = 0;
	if(0 == right_flag)
	{
		for(i = 0; i < CODEWORD_LEN; i++)
		{
			if(encoded_polynomial[i] == received_polynomial[i])
			{
				continue;
			}
			
			symbol_err_cnt++;
			for(j = 0; j < CODEWORD_LEN; j++)
			{
				if(i == chnl_rel_order_idx[j])
				{
					element_idx = j;
					break;
				}
			}
			if(YITA > element_idx)//in unrel. group
			{
				if((encoded_polynomial[i] != 0xFF)
					&& (encoded_polynomial[i] == (chnl_rel_thr_id[i] - 1)))
				{
					thr_cnt++;
				}
				if((encoded_polynomial[i] == 0xFF)
					&& (0 == chnl_rel_thr_id[i]))
				{
					thr_cnt++;
				}
			}

			if(0xFF == encoded_polynomial[i])
			{
				element_idx = 0;
			}
			else
			{
				element_idx = encoded_polynomial[i] + 1;
			}
			for(j = 0; j < GF_FIELD; j++)
			{
				if((chnl_rel_matrix[j][i]) > (chnl_rel_matrix[element_idx][i]))
				{
					right_compare_cnt++;
				}
			}

			for(j = 0; j < CODEWORD_LEN; j++)
			{
				if(i == chnl_rel_order_idx[j])
				{
					element_idx = j;
					break;
				}
			}

			DEBUG_INFO("err_condition: %ld | %ld %ld %ld | %ld | %ld | %ld\n",
					  i,
					  chnl_rel_max_id[i] - 1,
					  chnl_rel_scd_id[i] - 1,
					  chnl_rel_thr_id[i] - 1,
					  encoded_polynomial[i],
					  element_idx,
					  right_compare_cnt);		  
		}

		if((((CODEWORD_LEN - MESSAGE_LEN) / 2 + 1) >= symbol_err_cnt)
			&& (YITA <= replace_cnt)
			&& (0 < thr_cnt))
		{
			DEBUG_INFO("err_condition_for_new_tst_vct: %ld %ld %ld\n",
				       symbol_err_cnt,
				       replace_cnt,
				       thr_cnt);
			satisfy_cnt++;
		}
	}
#endif

#if 0
	for(i = 0; i < MESSAGE_LEN; i++)
	{
		if(decoded_message[i] != message_polynomial[i])
		{
			break;
		}
	}
	long long div_scale = 2;
	if(MESSAGE_LEN == i)
	{
		if(best_place > (pow_val / div_scale))
		{
			DEBUG_INFO("best_place_outer: %ld\n", best_place);
		}
	}
#endif
	
#if (1 == TEST_MODE)
	for(i = 0; i < pow_val; i++)
	{
		DEBUG_IMPOTANT("hamm_1: %ld | %ld\n",
		          i,
		          hamm_distance_code_cal(uncommon_decoded_codeword[best_place],
		                                 uncommon_decoded_codeword[i],
		                                 CODEWORD_LEN));
		DEBUG_IMPOTANT("hamm_2: %ld | %ld\n",
		          i,
		          hamm_distance_code_cal(uncommon_decoded_codeword[best_place],
		                                 tst_vct[i],
		                                 CODEWORD_LEN));
	}
#endif

	return 0;
}

int g_term_malloc()
{
	long long i = 0, j = 0, k = 0;

	long long lex_order_table[500][50];
	lex_order((long long **)lex_order_table, 500, 50, MESSAGE_LEN - 1);
	long long s_x = 0;
	for(i = 0; i < 500; i++)
	{
		for(j = 0; j < 50; j++)
		{
			if(lex_order_table[i][j] < (S_MUL * (S_MUL + 1) / 2 * CODEWORD_LEN))
			{
				if(s_x < i)
				{
					s_x = i;
				}
			}
		}
	}
	term_size_y = (long long)((S_MUL + 0.5) * sqrt(CODEWORD_LEN / (MESSAGE_LEN - 1))) + 2;
	term_size_x = s_x + term_size_y * (MESSAGE_LEN + 1) + 2;
	//term_size_x = 5;
	DEBUG_SYS("term_size: %ld %ld\n", term_size_x, term_size_y);

	g_term_c_p = (unsigned char***)malloc(sizeof(unsigned char**) * LAYER_NUM);
	for (i = 0; i < LAYER_NUM; i++)
	{
		DEBUG_SYS("malloc g_term: %d\n", i);
	
  		g_term_c_p[i] = (unsigned char**)malloc(sizeof(unsigned char*) * POLY_NUM);

		for(j = 0; j < POLY_NUM; j++)
		{
			g_term_c_p[i][j] = (unsigned char*)malloc(sizeof(unsigned char) * (term_size_x * term_size_y));
		}
  	}

	g_term_x = (long long*)malloc(sizeof(long long) * (term_size_x * term_size_y));
	g_term_y = (long long*)malloc(sizeof(long long) * (term_size_x * term_size_y));
	
	k = 0;
	for(i = 0; i < term_size_x; i++)
	{
		for(j = 0; j < term_size_y; j++)
		{
			g_term_x[k] = i;
			g_term_y[k] = j;
			k++;
		}
	}
	
	DEBUG_SYS("malloc g_term OK\n");
	
	skip_hist = (long long*)malloc(sizeof(long long) * pow_val);
	pgd_hist = (long long*)malloc(sizeof(long long) * pow_val);
#if (1 == CFG_ADAPTIVE_PARALLEL)
	round_hist = (long long*)malloc(sizeof(long long) * (pow_val + 1));
#else
	round_hist = (long long*)malloc(sizeof(long long) * (pow_val / PARALLEL_BATCH_NUM + 1));
#endif
	
	return 0;
}

int g_term_destroy()
{
	long long i = 0, j = 0;

	for (i = 0; i < LAYER_NUM; i++)
	{
		for(j = 0; j < POLY_NUM; j++)
		{
			free(g_term_c_p[i][j]);
			g_term_c_p[i][j] = NULL;;
			//DEBUG_NOTICE("free: %ld %ld\n", i, j);
		}

		free(g_term_c_p[i]);
		g_term_c_p[i] = NULL;
	}
	free(g_term_c_p);
	g_term_c_p = NULL;

	free(g_term_x);
	g_term_x = NULL;
	free(g_term_y);
	g_term_y = NULL;
	
	free(skip_hist);
	skip_hist = NULL;
	free(pgd_hist);
	pgd_hist = NULL;
	free(round_hist);
	round_hist = NULL;

	return 0;
}

int g_term_init()
{
	long long i = 0, j = 0, k = 0;

	clock_t start, stop;
	float runtime;
	start = clock();
	
	for(k = 0; k < LAYER_NUM; k++)
	{
#if 0		
		for(j = 0; j < (term_size_x * term_size_y); j++)
		{
#if 0			
			//for(j = 0; j < (term_size_x * term_size_y); j++)
			for(i = 0; i < POLY_NUM; i++)
			{
				g_term_c[k][i][j] = 0xFF;
			}
#endif			
			g_term_0_y_c[k][j] = 0xFF;
			g_term_x_0_c[k][j] = 0xFF;
#if 0
			for(i = 0; i < POLY_NUM; i++)
			{
				g_term_c_p[k][i][j] = 0xFF;
			}
#endif
		}
#endif

#if (0 == RECUR_RR)
		memset(g_term_0_y_c[k], 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));
		memset(g_term_x_0_c[k], 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));
#endif
		for(i = 0; i < POLY_NUM; i++)
		{
			memset(g_term_c_p[k][i], 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));
		}
	}

	hamm_distance_debug = 0x7FFF;

	stop = clock();
	runtime = (stop - start) / 1000.0000;
	//DEBUG_SYS("Time_g_term_init: %fs\n", runtime);
	//DEBUG_SYS("g_term_init OK\n");
	return 0;
}

#if (0 == RECUR_RR)
int f_root_init()
{
	long long i = 0, j = 0;

	for(i = 0; i < ROOT_SIZE; i++)
	{
#if 0		
		for(j = 0; j < ROOT_SIZE; j++)
		{
			f_root_val[i][j] = 0xFF;
			f_root_prev[i][j] = 0xFF;
		}
#else
		memset(f_root_val[i], 0xFF, sizeof(unsigned char) * ROOT_SIZE);
		memset(f_root_prev[i], 0xFF, sizeof(unsigned char) * ROOT_SIZE);
#endif
		f_root_cnt[i + 1] = 0;
	}
	f_root_cnt[0] = 1;
	
	return 0;
}

int g_term_new_gen(long long layer_idx, long long tern_idx, unsigned char root_insert)
{
	long long i = 0, j = 0, k = 0, l = 0, r = 0, s = 0;

	unsigned char tmp = 0xFF;
	unsigned char g_term_c_expand[term_size_x * term_size_y];
	unsigned char tmp_g_term_c_expand[term_size_x * term_size_y];
	unsigned char mul_g_term_c_expand[term_size_x * term_size_y];
	unsigned char g_term_c_expand_store[term_size_x * term_size_y];
	for(k = 0; k < (term_size_x * term_size_y); k++)
	{
#if 0		
		if((1 == g_term_x[k])
			&& (1 == g_term_y[k]))
		{
			g_term_c_expand[k] = 0x0;
		}
		else if((0 == g_term_x[k])
			&& (0 == g_term_y[k]))
		{
			g_term_c_expand[k] = root_insert;
		}
		else
		{
			g_term_c_expand[k] = 0xFF;
		}

		mul_g_term_c_expand[k] = g_term_c_expand[k];
#else
		if((1 == g_term_x[k])
			&& (1 == g_term_y[k]))
		{
			mul_g_term_c_expand[k] = 0x0;
			g_term_c_expand[k] = 0xFF;
			DEBUG_NOTICE("g_term_init: %d %d | %x %x\n",
					g_term_x[k],
					g_term_y[k],
					g_term_c_expand[k],
					mul_g_term_c_expand[k]);
		}
		else if((0 == g_term_x[k])
			&& (0 == g_term_y[k]))
		{
			mul_g_term_c_expand[k] = root_insert;
			g_term_c_expand[k] = 0x0;
			DEBUG_NOTICE("g_term_init: %d %d | %x %x\n",
					g_term_x[k],
					g_term_y[k],
					g_term_c_expand[k],
					mul_g_term_c_expand[k]);
		}
		else
		{
			mul_g_term_c_expand[k] = 0xFF;
			g_term_c_expand[k] = 0xFF;
		}
#endif
		g_term_c_expand_store[k] = 0xFF;
		tmp_g_term_c_expand[k] = 0xFF;
	}

	/*init another g*/
	if((0 == layer_idx)
		&& (0 != tern_idx))
	{
#if 0		
		memcpy(g_term_c[layer_idx][tern_idx],
			   g_term_c[layer_idx][tern_idx - 1],
			   sizeof(unsigned char) * k);
#else
		memcpy(g_term_c_p[g_term_phase][tern_idx],
			   g_term_c_p[g_term_phase][tern_idx - 1],
			   sizeof(unsigned char) * k);
#endif
	}

	for(k = 0; k < (term_size_x * term_size_y); k++)//for every term contain "y"
	{
		if(0 == k)
		{
			DEBUG_NOTICE("g_term_check_err_k_1: %d | %d %d\n",
			k,
			g_term_x[k],
			g_term_y[k]);
			if((0 != g_term_x[k])
				|| (0 != g_term_y[k]))
			{
				while(1);
			}
		}

#if 0
		g_term_c[layer_idx + 1][tern_idx][k] = g_term_c[layer_idx][tern_idx][k];
#else
		g_term_c_p[phase_trans(g_term_phase)][tern_idx][k] = g_term_c_p[g_term_phase][tern_idx][k];
#endif

		if(0 == k)
		{
			DEBUG_NOTICE("g_term_check_err_k_2: %d %d %d | %d | %d %d\n",
			layer_idx,
			tern_idx,
			POLY_NUM,
			k,
			g_term_x[k],
			g_term_y[k]);
			if((0 != g_term_x[k])
				|| (0 != g_term_y[k]))
			{
				while(1);
			}
		}
		
		if((0 != g_term_y[k])
#if 0			
			&& (0xFF != g_term_c[layer_idx][tern_idx][k]))
#else			
			&& (0xFF != g_term_c_p[g_term_phase][tern_idx][k]))
#endif			
		{
			DEBUG_NOTICE("*********************\n");
			DEBUG_NOTICE("g_term_have_y: %d | %d %d | %x\n",
		    tern_idx,
		    g_term_x[k],
		    g_term_y[k],
#if 0
		    g_term_c[layer_idx][tern_idx][k]);
#else
			g_term_c_p[g_term_phase][tern_idx][k]);
#endif
			
			for(l = 0; l < (g_term_y[k] - 0); l++)//for pow_cal, g*m => tmp
			{
				//DEBUG_NOTICE("*********************\n");
				for(i = 0; i < (term_size_x * term_size_y); i++)//for every a
				{
					if(0 == i)
					{
						DEBUG_NOTICE("g_term_check_err_i: %ld | %ld %ld | %x\n",
						i,
						g_term_x[i],
						g_term_y[i],
						g_term_c_expand[i]);
						if((0 != g_term_x[i])
							|| (0 != g_term_y[i]))
						{
							while(1);
						}
					}
					
					if(0xFF != g_term_c_expand[i])
					{
						DEBUG_NOTICE("g_term_c_expand: %ld | %ld %ld | %x\n",
						i,
					    g_term_x[i],
					    g_term_y[i],
					    g_term_c_expand[i]);

						for(j = 0; j < (term_size_x * term_size_y); j++)//for every b
						{
							if(0xFF != mul_g_term_c_expand[j])
							{
								DEBUG_NOTICE("mul_g_term_c_expand: %d %d | %x\n",
							    g_term_x[j],
							    g_term_y[j],
							    mul_g_term_c_expand[j]);

								for(r = 0; r < (term_size_x * term_size_y); r++)//find the place
								{
									if(((g_term_x[i] + g_term_x[j]) == g_term_x[r])
										&& ((g_term_y[i] + g_term_y[j]) == g_term_y[r]))//r <= place(i, j)
									{
										tmp_g_term_c_expand[r] = gf_add(tmp_g_term_c_expand[r], gf_multp(g_term_c_expand[i], mul_g_term_c_expand[j]));
										DEBUG_NOTICE("tmp_g_term_c_expand: %d %d | %x\n",
											     g_term_x[r],
											     g_term_y[r],
											     tmp_g_term_c_expand[r]);
										break;
									}
								}
							}
						}
					}
				}

				/*after every mulp cal, copy and clear*/
				for(r = 0; r < (term_size_x * term_size_y); r++)
				{
					g_term_c_expand[r] = tmp_g_term_c_expand[r];
					tmp_g_term_c_expand[r] = 0xFF;
#if (1 == CFG_DEBUG_NOTICE)
					if(0xFF != g_term_c_expand[r])
					{
						DEBUG_NOTICE("g_term_expand_update: %d %d | %x\n",
							    g_term_x[r],
							    g_term_y[r],
							    g_term_c_expand[r]);
					}
#endif					
				}
			}

			for(r = 0; r < (term_size_x * term_size_y); r++)
			{
				if(0xFF != g_term_c_expand[r])
				{
					for(s = 0; s < (term_size_x * term_size_y); s++)
					{
						if(((g_term_x[r] + g_term_x[k]) == g_term_x[s])
						&& (g_term_y[r] == g_term_y[s]))
						{
							DEBUG_NOTICE("g_term_expand_store updating: %d + %d = %d, %d | %x %x %x\n",
								    g_term_x[r],
								    g_term_x[k],
							    	g_term_x[s],
							    	g_term_y[s],
							    	g_term_c_expand[r],
#if 0
							    	g_term_c[layer_idx][tern_idx][k],
#else
							    	g_term_c_p[g_term_phase][tern_idx][k],
#endif
							    	g_term_c_expand_store[s]);
							//g_term_c_expand_store[s] = gf_add(g_term_c_expand_store[s], g_term_c_expand[r]);
							//g_term_c_expand_store[s] = gf_multp(g_term_c_expand_store[s], g_term_c[layer_idx][tern_idx][k]);
#if 0
							tmp = gf_multp(g_term_c_expand[r], g_term_c[layer_idx][tern_idx][k]);
#else
							tmp = gf_multp(g_term_c_expand[r], g_term_c_p[g_term_phase][tern_idx][k]);
#endif
							g_term_c_expand_store[s] = gf_add(g_term_c_expand_store[s], tmp);
							DEBUG_NOTICE("g_term_expand_store: %d %d | %x\n",
							    	g_term_x[s],
							    	g_term_y[s],
							    	g_term_c_expand_store[s]);
						}
					}
					g_term_c_expand[r] = 0xFF;
				}
			}

			for(r = 0; r < (term_size_x * term_size_y); r++)
			{
#if 0		
				if((1 == g_term_x[r])
					&& (1 == g_term_y[r]))
				{
					g_term_c_expand[r] = 0x0;
				}
				else if((0 == g_term_x[r])
					&& (0 == g_term_y[r]))
				{
					g_term_c_expand[r] = root_insert;
				}
				else
				{
					g_term_c_expand[r] = 0xFF;
				}

				mul_g_term_c_expand[r] = g_term_c_expand[r];
#else
				if((1 == g_term_x[r])
					&& (1 == g_term_y[r]))
				{
					mul_g_term_c_expand[r] = 0x0;
					g_term_c_expand[r] = 0xFF;
				}
				else if((0 == g_term_x[r])
					&& (0 == g_term_y[r]))
				{
					mul_g_term_c_expand[r] = root_insert;
					g_term_c_expand[r] = 0x0;
				}
				else
				{
					mul_g_term_c_expand[r] = 0xFF;
					g_term_c_expand[r] = 0xFF;
				}
#endif
				//g_term_c_expand_store[r] = 0xFF;
				tmp_g_term_c_expand[r] = 0xFF;
			}

			/*clear terms have y*/
#if 0			
			g_term_c[layer_idx + 1][tern_idx][k] = 0xFF;
#else
			g_term_c_p[phase_trans(g_term_phase)][tern_idx][k] = 0xFF;
#endif
		}
	}

	DEBUG_NOTICE("*********************\n");
	/*update g_term*/
	for(r = 0; r < (term_size_x * term_size_y); r++)
	{
#if 0
		if((0 != g_term_y[r])
			&& (0xFF != g_term_c[tern_idx][r]))
		{
			g_term_c[tern_idx][r] = 0xFF;
		}
#endif
#if 0
		g_term_c[layer_idx + 1][tern_idx][r] = gf_add(g_term_c_expand_store[r], g_term_c[layer_idx + 1][tern_idx][r]);
#else
		g_term_c_p[phase_trans(g_term_phase)][tern_idx][r] = gf_add(g_term_c_expand_store[r], g_term_c_p[phase_trans(g_term_phase)][tern_idx][r]);
#endif
#if (1 == CFG_DEBUG_NOTICE)
#if 0
		if(0xFF != g_term_c[layer_idx + 1][tern_idx][r])
#else
		if(0xFF != g_term_c_p[phase_trans(g_term_phase)][tern_idx][r])
#endif
		{
			DEBUG_NOTICE("g_term_update: %d | %d %d | %x\n",
				    tern_idx,
				    g_term_x[r],
				    g_term_y[r],
#if 0
				    g_term_c[layer_idx + 1][tern_idx][r]);
#else
					g_term_c_p[phase_trans(g_term_phase)][tern_idx][r]);
#endif
		}
#endif		
	}

	DEBUG_NOTICE("*********************\n");
	/*eliminate common factor*/
	unsigned char cmn_factor = 0xFF;//deal with x
	for(r = 0; r < (term_size_x * term_size_y); r++)
	{
#if 0		
		if(0xFF != g_term_c[layer_idx + 1][tern_idx][r])
#else
		if(0xFF != g_term_c_p[phase_trans(g_term_phase)][tern_idx][r])
#endif
		{
			if(cmn_factor > g_term_x[r])
			{
				cmn_factor = g_term_x[r];
			}
		}
	}
	DEBUG_NOTICE("cmn_factor for x: %d\n", cmn_factor);
	if(0 != cmn_factor)
	{
		for(r = 0; r < (term_size_x * term_size_y); r++)
		{
#if 0
			if(0xFF != g_term_c[layer_idx + 1][tern_idx][r])
#else
			if(0xFF != g_term_c_p[phase_trans(g_term_phase)][tern_idx][r])
#endif
			{
				for(s = 0; s < (term_size_x * term_size_y); s++)
				{
					if((g_term_x[s] == (g_term_x[r] - cmn_factor))
						&& (g_term_y[s] == g_term_y[r]))
					{
#if 0
						g_term_c[layer_idx + 1][tern_idx][s] = g_term_c[layer_idx + 1][tern_idx][r];
						g_term_c[layer_idx + 1][tern_idx][r] = 0xFF;
						DEBUG_NOTICE("g_term_update_x: %d | %d %d | %x\n",
							    tern_idx,
							    g_term_x[s],
							    g_term_y[s],
							    g_term_c[layer_idx + 1][tern_idx][s]);
#else
						g_term_c_p[phase_trans(g_term_phase)][tern_idx][s] = g_term_c_p[phase_trans(g_term_phase)][tern_idx][r];
						g_term_c_p[phase_trans(g_term_phase)][tern_idx][r] = 0xFF;
						DEBUG_NOTICE("g_term_update_x: %d | %d %d | %x\n",
							    tern_idx,
							    g_term_x[s],
							    g_term_y[s],
							    g_term_c_p[phase_trans(g_term_phase)][tern_idx][s]);
#endif
						break;
					}
				}
			}
		}
	}
#if 0//you cannot deal with y, since y may be 0
	cmn_factor = 0xFF;//deal with y
	for(r = 0; r < (term_size_x * term_size_y); r++)
	{
		if(0xFF != g_term_c[tern_idx][r])
		{
			if(cmn_factor > g_term_y[r])
			{
				cmn_factor = g_term_y[r];
			}
		}
	}
	DEBUG_NOTICE("cmn_factor for y: %d\n", cmn_factor);
	if(0 != cmn_factor)
	{
		for(r = 0; r < (term_size_x * term_size_y); r++)
		{
			if(0xFF != g_term_c[tern_idx][r])
			{
				for(s = 0; s < (term_size_x * term_size_y); s++)
				{
					if((g_term_y[s] == (g_term_y[r] - cmn_factor))
						&& (g_term_x[s] == g_term_x[r]))
					{
						g_term_c[tern_idx][s] = g_term_c[tern_idx][r];
						g_term_c[tern_idx][r] = 0xFF;
						DEBUG_NOTICE("g_term_update_y: %d | %d %d | %x\n",
							    tern_idx,
							    g_term_x[s],
							    g_term_y[s],
							    g_term_c[tern_idx][s]);
						break;
					}
				}
			}
		}
	}
#endif

#if (1 == CFG_DEBUG_NOTICE)
	DEBUG_NOTICE("*********************\n");
	for(r = 0; r < (term_size_x * term_size_y); r++)
	{
#if 0
		if(0xFF != g_term_c[layer_idx + 1][tern_idx][r])
		{
			DEBUG_INFO("g_term_update_OK: %d | %d %d | %x\n",
				    tern_idx,
				    g_term_x[r],
				    g_term_y[r],
				    g_term_c[layer_idx + 1][tern_idx][r]);
		}
#else
		if(0xFF != g_term_c_p[phase_trans(g_term_phase)][tern_idx][r])
		{
			DEBUG_INFO("g_term_update_OK: %d | %d %d | %x\n",
				    tern_idx,
				    g_term_x[r],
				    g_term_y[r],
				    g_term_c_p[phase_trans(g_term_phase)][tern_idx][r]);
		}
#endif
	}
#endif
	
	return 0;
}

int g_term_0_y_cal(long long layer_idx, long long tern_idx)
{
	long long i = 0, j = 0;

#if 0
	/*clear*/
	for(i = 0; i < POLY_NUM; i++)
	{
		for(j = 0; j < (term_size_x * term_size_y); j++)
		{
			g_term_0_y_c[i][j] = 0xFF;
		}
	}

	for(i = 0; i < POLY_NUM; i++)
	{
		for(j = 0; j < (term_size_x * term_size_y); j++)
		{
			if((0 != g_term_x[j])
				&& (0xFF != g_term_c[i][j]))
			{
				g_term_0_y_c[i][j] = 0xFF;
				DEBUG_NOTICE("g_term_set_to_zero: %d | %d %d | %x %x\n",
					    i,
					    g_term_x[j],
					    g_term_y[j],
					    g_term_c[i][j],
					    g_term_0_y_c[i][j]);
			}
			else
			{
				g_term_0_y_c[i][j] = g_term_c[i][j];
				if(0xFF != g_term_0_y_c[i][j])
				{
					DEBUG_NOTICE("g_term_0_y: %d | %d %d | %x\n",
							i,
							g_term_x[j],
							g_term_y[j],
							g_term_0_y_c[i][j]);
				}
			}
		}
	}
#else
	/*clear*/
#if 0
	for(j = 0; j < (term_size_x * term_size_y); j++)
	{
		//DEBUG_INFO("layer_idx: %ld, j: %ld\n", layer_idx, j);
		g_term_0_y_c[layer_idx][j] = 0xFF;
	}
#else
	memset(g_term_0_y_c[layer_idx], 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));
#endif

	for(j = 0; j < (term_size_x * term_size_y); j++)
	{
		if(0 == j)
		{
			DEBUG_NOTICE("g_term_check_err_j: %d | %d %d\n",
			j,
			g_term_x[j],
			g_term_y[j]);
			if((0 != g_term_x[j])
				|| (0 != g_term_y[j]))
			{
				while(1);
			}
		}
		
		if((0 != g_term_x[j])
#if 0
			&& (0xFF != g_term_c[layer_idx][tern_idx][j]))
#else
			&& (0xFF != g_term_c_p[g_term_phase][tern_idx][j]))
#endif
		{
			g_term_0_y_c[layer_idx][j] = 0xFF;
			DEBUG_NOTICE("g_term_set_to_zero: %d | %d %d | %x %x\n",
				    i,
				    g_term_x[j],
				    g_term_y[j],
#if 0
				    g_term_c[layer_idx][tern_idx][j],
#else
					g_term_c_p[g_term_phase][tern_idx][j],
#endif
				    g_term_0_y_c[layer_idx][j]);
		}
		else
		{
#if 0
			g_term_0_y_c[layer_idx][j] = g_term_c[layer_idx][tern_idx][j];
#else
			g_term_0_y_c[layer_idx][j] = g_term_c_p[g_term_phase][tern_idx][j];
#endif
#if (1 == CFG_DEBUG_NOTICE)
			if(0xFF != g_term_0_y_c[layer_idx][j])
			{
				DEBUG_NOTICE("g_term_0_y: %d | %d %d | %x\n",
						i,
						g_term_x[j],
						g_term_y[j],
						g_term_0_y_c[layer_idx][j]);
			}
#endif
		}
	}
#endif

	return 0;
}

unsigned char g_term_x_0_cal(long long layer_idx, long long tern_idx)
{
	unsigned char val = 0xFF;

	long long i = 0, j = 0;

	/*clear*/
#if 0	
	for(j = 0; j < (term_size_x * term_size_y); j++)
	{
		g_term_x_0_c[layer_idx][j] = 0xFF;
	}
#else
	memset(g_term_x_0_c[layer_idx], 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));
#endif

	for(j = 0; j < (term_size_x * term_size_y); j++)
	{
		if((0 != g_term_y[j])
#if 0
			&& (0xFF != g_term_c[layer_idx][tern_idx][j]))
#else
			&& (0xFF != g_term_c_p[g_term_phase][tern_idx][j]))
#endif
		{
			g_term_x_0_c[layer_idx][j] = 0xFF;
#if 0			
			DEBUG_NOTICE("g_term_set_to_zero: %d | %d %d | %x %x\n",
				    i,
				    g_term_x[j],
				    g_term_y[j],
				    g_term_c[layer_idx][tern_idx][j],
				    g_term_x_0_c[layer_idx][tern_idx][j]);
#endif
		}
		else
		{
#if 0
			g_term_x_0_c[layer_idx][j] = g_term_c[layer_idx][tern_idx][j];
#else
			g_term_x_0_c[layer_idx][j] = g_term_c_p[g_term_phase][tern_idx][j];
#endif
#if 0
			if(0xFF != g_term_x_0_c[layer_idx][tern_idx][j])
			{
				DEBUG_NOTICE("g_term_0_y: %d | %d %d | %x\n",
						i,
						g_term_x[j],
						g_term_y[j],
						g_term_x_0_c[layer_idx][tern_idx][j]);
			}
#endif			
		}

		val = gf_add(val, g_term_x_0_c[layer_idx][j]);
	}
	
	return val;
}

int chien_searching_for_g_0_y(long long layer_idx, long long tern_idx, unsigned char root_test)
{
	long long is_root = 0;
	long long k = 0;
	unsigned char tmp = 0xFF, tmp_sum = 0xFF;
	
	for(k = 0; k < (term_size_x * term_size_y); k++)
	{
		if(0xFF != g_term_0_y_c[layer_idx][k])
		{
			tmp = 0xFF;
			tmp = gf_pow_cal(root_test, g_term_y[k]);
			//DEBUG_NOTICE("tmp: %x | %x^%d\n", tmp, root_test, g_term_y[k]);
			//DEBUG_NOTICE("tmp: %x | %x*%x\n", gf_multp(tmp, g_term_0_y_c[tern_idx][k]), tmp, g_term_0_y_c[tern_idx][k]);
			tmp = gf_multp(tmp, g_term_0_y_c[layer_idx][k]);
			//DEBUG_NOTICE("tmp_sum: %x | %x+%x\n", gf_add(tmp_sum, tmp), tmp_sum, tmp);
			tmp_sum = gf_add(tmp_sum, tmp);
		}
	}

	if(0xFF == tmp_sum)
	{
		is_root = 1;
		DEBUG_INFO("is_root: %d %x\n", tern_idx, root_test);
	}
	else
	{
		is_root = 0;
	}

	return is_root;
}

int rr_factorization()
{
	long long i = 0, j = 0, k = 0, l = 0, r = 0, s = 0;
	long long is_root = 0;
#if (0 == RECUR_RR)
	rr_err = 0;
#endif
	//test_factorization_init();
	f_root_init();

	//chien_searching_for_g_0_y(1, power_polynomial_table[0][0]);//test
	//g_term_new_gen(1, power_polynomial_table[0][0]);//test

	for(s = 0; s < MESSAGE_LEN; s++)//layer
	{
		DEBUG_INFO("-------------------------------------------\n");
		//DEBUG_INFO("Layer: %ld, g_term_phase: %ld\n", s, g_term_phase);
		l = 0;
		for(r = 0; r < f_root_cnt[s]; r++)//roots per layer
		{
			//DEBUG_INFO("Root: %ld, f_root_cnt: %ld\n", r, f_root_cnt[s]);
			g_term_0_y_cal(s, r);

			for(k = 0; k < GF_FIELD; k++)//test roots
			{
				is_root = chien_searching_for_g_0_y(s, r, power_polynomial_table[k][0]);
				if(1 == is_root)
				{
					f_root_val[s][l] = power_polynomial_table[k][0];
					f_root_prev[s][l] = r;
					f_root_cnt[s + 1] = f_root_cnt[s + 1] + 1;

					DEBUG_INFO("f_root: %d %d | %x | %x | %d\n",
								s,
								l,
								f_root_val[s][l],
								f_root_prev[s][l],
								f_root_cnt[s + 1]);

					g_term_new_gen(s, l, f_root_val[s][l]);

					l = l + 1;
					if(POLY_NUM <= l)
					{
						/*just exit*/
						k = GF_FIELD;
						r = f_root_cnt[s];
#if (0 == RECUR_RR)						
						if(0 == rr_err)
						{
							rr_err = 1;
						}
#endif						
					}
				}
			}
		}

		/*phase trans.*/
		if(0 == g_term_phase)
		{
			g_term_phase = 1;
		}
		else
		{
			g_term_phase = 0;
		}
	}

	return 0;
}

int check_rr_decoded_result()
{
	long long r = 0, s = 0, prev_r = 0;
	long long hamm_distance_code = 0x7FFF, hamm_distance_bit = 0x7FFF, tmp_code = 0, tmp_bit = 0;
	unsigned char tmp_decoded_message[MESSAGE_LEN];
	unsigned char tmp_decoded_codeword[CODEWORD_LEN];
	//long long hamm_distance_debug = 0x7FFF;

	memset(tmp_decoded_message, 0xFF, sizeof(unsigned char) * MESSAGE_LEN);
	memset(tmp_decoded_codeword, 0xFF, sizeof(unsigned char) * CODEWORD_LEN);

	for(r = 0; r < f_root_cnt[MESSAGE_LEN]; r++)
	{
		if(0xFF == g_term_x_0_cal(MESSAGE_LEN, r))
		{
			DEBUG_IMPOTANT("Decoding OK!\n");
			if(1 == decoding_ok_flag)
			{
				decoding_ok_flag = 2;
			}

			DEBUG_IMPOTANT("Message: %d %d | %x\n", MESSAGE_LEN - 1, r, f_root_val[MESSAGE_LEN - 1][r]);

			memset(tmp_decoded_message, 0xFF, sizeof(unsigned char) * MESSAGE_LEN);
			tmp_decoded_message[MESSAGE_LEN - 1] = f_root_val[MESSAGE_LEN - 1][r];

			prev_r = r;
			for(s = MESSAGE_LEN - 2; s >= 0; s--)
			{
				DEBUG_IMPOTANT("Message: %d %d | %x\n", s, prev_r, f_root_val[s][f_root_prev[s + 1][prev_r]]);

				tmp_decoded_message[s] = f_root_val[s][f_root_prev[s + 1][prev_r]];

				prev_r = f_root_prev[s + 1][prev_r];
			}

			evaluation_encoding_v2(tmp_decoded_message, tmp_decoded_codeword);

			tmp_code = hamm_distance_code_cal(tmp_decoded_codeword, received_polynomial, CODEWORD_LEN);
			//tmp_code = (long long)euc_distance_code_cal(tmp_decoded_codeword, recv_seq, CODEWORD_LEN);
			tmp_bit = hamm_distance_bit_cal(tmp_decoded_codeword, received_polynomial, CODEWORD_LEN);
			if(tmp_code < hamm_distance_code)
			{
				hamm_distance_code = tmp_code;
				hamm_distance_bit = tmp_bit;
				memcpy(decoded_codeword, tmp_decoded_codeword, sizeof(unsigned char) * CODEWORD_LEN);
#if (1 == SYS_ENC)				
				memcpy(decoded_message, (tmp_decoded_codeword + (CODEWORD_LEN - MESSAGE_LEN)), sizeof(unsigned char) * MESSAGE_LEN);
#else
				memcpy(decoded_message, tmp_decoded_message, sizeof(unsigned char) * MESSAGE_LEN);
#endif
			}
			if(tmp_code == hamm_distance_code)
			{
				if(tmp_bit < hamm_distance_bit)
				{
					hamm_distance_bit = tmp_bit;
					memcpy(decoded_codeword, tmp_decoded_codeword, sizeof(unsigned char) * CODEWORD_LEN);
#if (1 == SYS_ENC)				
					memcpy(decoded_message, (tmp_decoded_codeword + (CODEWORD_LEN - MESSAGE_LEN)), sizeof(unsigned char) * MESSAGE_LEN);
#else
					memcpy(decoded_message, tmp_decoded_message, sizeof(unsigned char) * MESSAGE_LEN);
#endif
				}
			}

			if(0 != hamm_distance_debug)
			{
				hamm_distance_debug = hamm_distance_code_cal(tmp_decoded_message, message_polynomial, MESSAGE_LEN);		
				DEBUG_IMPOTANT("Hamming Distance Debug: %ld\n", hamm_distance_debug);
			}
		}
		else
		{
			DEBUG_IMPOTANT("Decoding Fail for Root-%d\n", r);
		}
	}

#if (1 == CFG_DEBUG_IMPOTANT)
	if(0x7FFF != hamm_distance_code)
	{
		DEBUG_IMPOTANT("Received Codeword:\n");
		for(r = 0; r < CODEWORD_LEN; r++)
		{
			DEBUG_IMPOTANT("%x ", received_polynomial[r]);
		}
		DEBUG_IMPOTANT("\n");

		DEBUG_IMPOTANT("Decoding Result:\n");
		for(r = 0; r < CODEWORD_LEN; r++)
		{
			DEBUG_IMPOTANT("%x ", decoded_codeword[r]);
		}
		DEBUG_IMPOTANT("\n");

		DEBUG_IMPOTANT("Hamming Distance: %ld %ld\n", hamm_distance_code, hamm_distance_bit);

		DEBUG_IMPOTANT("Decoded Message:\n");
		for(r = 0; r < MESSAGE_LEN; r++)
		{
			DEBUG_IMPOTANT("%x ", decoded_message[r]);
		}
		DEBUG_IMPOTANT("\n");
	}
	else
	{
		DEBUG_IMPOTANT("Decoding Fail!\n");
	}
#endif

	return 0;
}
#endif

int chien_searching_for_g_0_y_recur(unsigned char *g_c_in, unsigned char root_test)
{
	long long is_root = 0;
	long long k = 0;
	unsigned char tmp = 0xFF, tmp_sum = 0xFF;
	
	for(k = 0; k < (term_size_x * term_size_y); k++)
	{
		if(0xFF != g_c_in[k])
		{
			tmp = 0xFF;
			tmp = gf_pow_cal(root_test, g_term_y[k]);
			//DEBUG_NOTICE("tmp: %x | %x^%d\n", tmp, root_test, g_term_y[k]);
			//DEBUG_NOTICE("tmp: %x | %x*%x\n", gf_multp(tmp, g_term_0_y_c[tern_idx][k]), tmp, g_term_0_y_c[tern_idx][k]);
			tmp = gf_multp(tmp, g_c_in[k]);
			//DEBUG_NOTICE("tmp_sum: %x | %x+%x\n", gf_add(tmp_sum, tmp), tmp_sum, tmp);
			tmp_sum = gf_add(tmp_sum, tmp);
		}
	}

	if(0xFF == tmp_sum)
	{
		is_root = 1;
		DEBUG_INFO("is_root: %x\n", root_test);
	}
	else
	{
		is_root = 0;
	}

	return is_root;
}

int g_term_0_y_cal_recur(unsigned char *g_c_in, unsigned char *g_c_out)
{
	long long i = 0, j = 0;

	/*clear*/
	memset(g_c_out, 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));

	for(j = 0; j < (term_size_x * term_size_y); j++)
	{	
		if((0 != g_term_x[j])
			&& (0xFF != g_c_in[j]))
		{
			g_c_out[j] = 0xFF;
			DEBUG_NOTICE("g_term_set_to_zero: %d | %d %d | %x %x\n",
					j,
					g_term_x[j],
					g_term_y[j],
					g_c_in[j],
					g_c_out[j]);
		}
		else
		{
			g_c_out[j] = g_c_in[j];
#if (1 == CFG_DEBUG_NOTICE)
			if(0xFF != g_c_out[j])
			{
				DEBUG_NOTICE("g_term_0_y: %d | %d %d | %x\n",
						j,
						g_term_x[j],
						g_term_y[j],
						g_c_out[j]);
			}
#endif
		}
	}

	return 0;
}

unsigned char g_term_x_0_cal_recur(unsigned char *g_c_in)
{
	unsigned char val = 0xFF;
	long long j = 0;
	
#if (1 == DYNAMIC_MEM)
	unsigned char *g_c_x_0;
	g_c_x_0 = (unsigned char*)malloc(sizeof(unsigned char) * (term_size_x * term_size_y));
#else
	unsigned char g_c_x_0[term_size_x * term_size_y];
#endif
	memset(g_c_x_0, 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));

	for(j = 0; j < (term_size_x * term_size_y); j++)
	{
		if((0 != g_term_y[j])
			&& (0xFF != g_c_in[j]))
		{
			g_c_x_0[j] = 0xFF;
		}
		else
		{
			g_c_x_0[j] = g_c_in[j];
		}

		val = gf_add(val, g_c_x_0[j]);
	}

#if (1 == DYNAMIC_MEM)
	free(g_c_x_0);
	g_c_x_0 = NULL;
#endif

	return val;
}

#if 0
unsigned char g_term_c_expand[8505];
unsigned char tmp_g_term_c_expand[8505];
unsigned char mul_g_term_c_expand[8505];
unsigned char g_term_c_expand_store[8505];
#endif
unsigned char *g_term_c_expand;
unsigned char *tmp_g_term_c_expand;
unsigned char *mul_g_term_c_expand;
unsigned char *g_term_c_expand_store;
int g_term_new_gen_recur(unsigned char *g_c_in, unsigned char root_insert)
{
	long long i = 0, j = 0, k = 0, l = 0, r = 0, s = 0;

	DEBUG_NOTICE("g_term_new_gen_recur: %ld %ld %x\n",
		        term_size_x, term_size_y, root_insert);

	unsigned char tmp = 0xFF;

	/*These global arrays are only actually used in this function.*/
	/*They are global to avoid stack overflow.*/
	g_term_c_expand = (unsigned char*)malloc(sizeof(unsigned char) * (term_size_x * term_size_y));
	tmp_g_term_c_expand = (unsigned char*)malloc(sizeof(unsigned char) * (term_size_x * term_size_y));
	mul_g_term_c_expand = (unsigned char*)malloc(sizeof(unsigned char) * (term_size_x * term_size_y));
	g_term_c_expand_store = (unsigned char*)malloc(sizeof(unsigned char) * (term_size_x * term_size_y));
	memset(g_term_c_expand, 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));
	memset(tmp_g_term_c_expand, 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));
	memset(mul_g_term_c_expand, 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));
	memset(g_term_c_expand_store, 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));

	for(k = 0; k < (term_size_x * term_size_y); k++)
	{
		if((1 == g_term_x[k])
			&& (1 == g_term_y[k]))
		{
			mul_g_term_c_expand[k] = 0x0;
			g_term_c_expand[k] = 0xFF;
			DEBUG_NOTICE("g_term_init: %d %d | %x %x\n",
					g_term_x[k],
					g_term_y[k],
					g_term_c_expand[k],
					mul_g_term_c_expand[k]);
		}
		else if((0 == g_term_x[k])
			&& (0 == g_term_y[k]))
		{
			mul_g_term_c_expand[k] = root_insert;
			g_term_c_expand[k] = 0x0;
			DEBUG_NOTICE("g_term_init: %d %d | %x %x\n",
					g_term_x[k],
					g_term_y[k],
					g_term_c_expand[k],
					mul_g_term_c_expand[k]);
		}
		else
		{
			mul_g_term_c_expand[k] = 0xFF;
			g_term_c_expand[k] = 0xFF;
		}
		g_term_c_expand_store[k] = 0xFF;
		tmp_g_term_c_expand[k] = 0xFF;
	}

	for(k = 0; k < (term_size_x * term_size_y); k++)//for every term contain "y"
	{		
		if((0 != g_term_y[k])			
			&& (0xFF != g_c_in[k]))	
		{
			DEBUG_NOTICE("*********************\n");
			DEBUG_NOTICE("g_term_have_y: %d | %d %d | %x\n",
		    k,
		    g_term_x[k],
		    g_term_y[k],
			g_c_in[k]);
			
			for(l = 0; l < g_term_y[k]; l++)//for pow_cal, g*m => tmp
			{
				//DEBUG_NOTICE("*********************\n");
				for(i = 0; i < (term_size_x * term_size_y); i++)//for every a
				{
					
					if(0xFF != g_term_c_expand[i])
					{
						DEBUG_NOTICE("g_term_c_expand: %ld | %ld %ld | %x\n",
						i,
					    g_term_x[i],
					    g_term_y[i],
					    g_term_c_expand[i]);

						for(j = 0; j < (term_size_x * term_size_y); j++)//for every b
						{
							if(0xFF != mul_g_term_c_expand[j])
							{
								DEBUG_NOTICE("mul_g_term_c_expand: %d %d | %x\n",
							    g_term_x[j],
							    g_term_y[j],
							    mul_g_term_c_expand[j]);

								for(r = 0; r < (term_size_x * term_size_y); r++)//find the place
								{
									if(((g_term_x[i] + g_term_x[j]) == g_term_x[r])
										&& ((g_term_y[i] + g_term_y[j]) == g_term_y[r]))//r <= place(i, j)
									{
										tmp_g_term_c_expand[r] = gf_add(tmp_g_term_c_expand[r], gf_multp(g_term_c_expand[i], mul_g_term_c_expand[j]));
										DEBUG_NOTICE("tmp_g_term_c_expand: %d %d | %x\n",
											     g_term_x[r],
											     g_term_y[r],
											     tmp_g_term_c_expand[r]);
										break;
									}
								}
							}
						}
					}
				}

				/*after every mulp cal, copy and clear*/
				for(r = 0; r < (term_size_x * term_size_y); r++)
				{
					g_term_c_expand[r] = tmp_g_term_c_expand[r];
					tmp_g_term_c_expand[r] = 0xFF;
#if (1 == CFG_DEBUG_NOTICE)
					if(0xFF != g_term_c_expand[r])
					{
						DEBUG_NOTICE("g_term_expand_update: %d %d | %x\n",
							    g_term_x[r],
							    g_term_y[r],
							    g_term_c_expand[r]);
					}
#endif
				}
			}

			for(r = 0; r < (term_size_x * term_size_y); r++)
			{
				if(0xFF != g_term_c_expand[r])
				{
					for(s = 0; s < (term_size_x * term_size_y); s++)
					{
						if(((g_term_x[r] + g_term_x[k]) == g_term_x[s])
						&& (g_term_y[r] == g_term_y[s]))
						{
							DEBUG_NOTICE("g_term_expand_store updating: %d + %d = %d, %d | %x %x %x\n",
								    g_term_x[r],
								    g_term_x[k],
							    	g_term_x[s],
							    	g_term_y[s],
							    	g_term_c_expand[r],
							    	g_c_in[k],
							    	g_term_c_expand_store[s]);
							tmp = gf_multp(g_term_c_expand[r], g_c_in[k]);
							g_term_c_expand_store[s] = gf_add(g_term_c_expand_store[s], tmp);
							DEBUG_NOTICE("g_term_expand_store: %d %d | %x\n",
							    	g_term_x[s],
							    	g_term_y[s],
							    	g_term_c_expand_store[s]);
						}
					}
					g_term_c_expand[r] = 0xFF;
				}
			}

			for(r = 0; r < (term_size_x * term_size_y); r++)
			{
				if((1 == g_term_x[r])
					&& (1 == g_term_y[r]))
				{
					mul_g_term_c_expand[r] = 0x0;
					g_term_c_expand[r] = 0xFF;
				}
				else if((0 == g_term_x[r])
					&& (0 == g_term_y[r]))
				{
					mul_g_term_c_expand[r] = root_insert;
					g_term_c_expand[r] = 0x0;
				}
				else
				{
					mul_g_term_c_expand[r] = 0xFF;
					g_term_c_expand[r] = 0xFF;
				}
				tmp_g_term_c_expand[r] = 0xFF;
			}

			/*clear terms have y*/
			g_c_in[k] = 0xFF;
		}
	}

	DEBUG_NOTICE("*********************\n");
	/*update g_term*/
	for(r = 0; r < (term_size_x * term_size_y); r++)
	{
		g_c_in[r] = gf_add(g_term_c_expand_store[r], g_c_in[r]);
#if (1 == CFG_DEBUG_NOTICE)
		if(0xFF != g_c_in[r])
		{
			DEBUG_NOTICE("g_term_update: %d | %d %d | %x\n",
				    r,
				    g_term_x[r],
				    g_term_y[r],
					g_c_in[r]);
		}
#endif		
	}

	DEBUG_NOTICE("*********************\n");
	/*eliminate common factor*/
	unsigned char cmn_factor = 0xFF;//deal with x
	for(r = 0; r < (term_size_x * term_size_y); r++)
	{
		if(0xFF != g_c_in[r])
		{
			if(cmn_factor > g_term_x[r])
			{
				cmn_factor = g_term_x[r];
			}
		}
	}
	DEBUG_NOTICE("cmn_factor for x: %d\n", cmn_factor);
	if(0 != cmn_factor)
	{
		for(r = 0; r < (term_size_x * term_size_y); r++)
		{
			if(0xFF != g_c_in[r])
			{
				for(s = 0; s < (term_size_x * term_size_y); s++)
				{
					if((g_term_x[s] == (g_term_x[r] - cmn_factor))
						&& (g_term_y[s] == g_term_y[r]))
					{
						g_c_in[s] = g_c_in[r];
						g_c_in[r] = 0xFF;
						DEBUG_NOTICE("g_term_update_x: %d | %d %d | %x\n",
							    s,
							    g_term_x[s],
							    g_term_y[s],
							    g_c_in[s]);
						break;
					}
				}
			}
		}
	}

#if (1 == CFG_DEBUG_NOTICE)
	DEBUG_NOTICE("*********************\n");
	for(r = 0; r < (term_size_x * term_size_y); r++)
	{
		if(0xFF != g_c_in[r])
		{
			DEBUG_INFO("g_term_update_OK: %d | %d %d | %x\n",
				    r,
				    g_term_x[r],
				    g_term_y[r],
				    g_c_in[r]);
		}
	}
#endif

	free(g_term_c_expand);
	g_term_c_expand = NULL;
	free(tmp_g_term_c_expand);
	tmp_g_term_c_expand = NULL;
	free(mul_g_term_c_expand);
	mul_g_term_c_expand = NULL;
	free(g_term_c_expand_store);
	g_term_c_expand_store = NULL;

	return 0;
}

int check_rr_decoded_result_recur(unsigned char *msg)
{
	long long i = 0;
	long long hamm_distance_code = 0x7FFF, hamm_distance_bit = 0x7FFF, tmp_code = 0, tmp_bit = 0;

#if (0 == RE_ENCODING)
	evaluation_encoding_v2(msg, tmp_codeword);
#else

#if (CFG_RR_MODE == BMA_RR)
	bm_re_encoding(msg, tmp_codeword);
#endif

#if (CFG_RR_MODE == CONV_RE_ENC_SYS)
	/*tmp_codeword has been calculated in dfs_rr_recur.*/
#endif

#if (CFG_RR_MODE >= CONV_RE_ENC)
	evaluation_encoding_v2(msg, tmp_codeword);
#endif

#endif

	for(i = 0; i < MESSAGE_LEN; i++)
	{
		DEBUG_NOTICE("msg: %ld %x\n", i, msg[i]);
	}
	for(i = 0; i < CODEWORD_LEN; i++)
	{
		DEBUG_NOTICE("tmp_decoded_codeword: %ld %x\n", i, tmp_codeword[i]);
	}

#if (1 == RE_ENCODING)
	tmp_code = hamm_distance_code_cal(tmp_codeword, received_polynomial, CODEWORD_LEN);
	tmp_bit = hamm_distance_bit_cal(tmp_codeword, received_polynomial, CODEWORD_LEN);
#else
	tmp_code = hamm_distance_code_cal(tmp_codeword, received_polynomial, CODEWORD_LEN);
	//tmp_code = (long long)euc_distance_code_cal(tmp_decoded_codeword, recv_seq, CODEWORD_LEN);
	tmp_bit = hamm_distance_bit_cal(tmp_codeword, received_polynomial, CODEWORD_LEN);
#endif

	DEBUG_NOTICE("distance: %d %d | %d %d\n", tmp_code, tmp_bit, best_hamm_distance_code, best_hamm_distance_bit);

	if(tmp_code < best_hamm_distance_code)
	{
		best_hamm_distance_code = tmp_code;
		best_hamm_distance_bit = tmp_bit;
		memcpy(decoded_codeword, tmp_codeword, sizeof(unsigned char) * CODEWORD_LEN);
#if (1 == SYS_ENC)				
		memcpy(decoded_message, (tmp_codeword + (CODEWORD_LEN - MESSAGE_LEN)), sizeof(unsigned char) * MESSAGE_LEN);
#else
		memcpy(decoded_message, msg, sizeof(unsigned char) * MESSAGE_LEN);
#endif
		//if(0 == hamm_distance_debug)
		{
			DEBUG_NOTICE("now best distance: %d %d\n", decoding_ok_flag, best_hamm_distance_code);
		}
	}
	if(tmp_code == best_hamm_distance_code)
	{
		if(tmp_bit < best_hamm_distance_bit)
		{
			best_hamm_distance_bit = tmp_bit;
			memcpy(decoded_codeword, tmp_codeword, sizeof(unsigned char) * CODEWORD_LEN);
#if (1 == SYS_ENC)				
			memcpy(decoded_message, (tmp_codeword + (CODEWORD_LEN - MESSAGE_LEN)), sizeof(unsigned char) * MESSAGE_LEN);
#else
			memcpy(decoded_message, msg, sizeof(unsigned char) * MESSAGE_LEN);
#endif

			//if(0 == hamm_distance_debug)
			{
				DEBUG_NOTICE("distance: %d %d\n", decoding_ok_flag, best_hamm_distance_code);
			}
		}
	}

#if 1//(0 == RE_ENCODING)
	//hamm_distance_debug = hamm_distance_code_cal(msg, message_polynomial, MESSAGE_LEN);
	hamm_distance_debug = hamm_distance_code_cal(tmp_codeword, encoded_polynomial, CODEWORD_LEN);
	DEBUG_NOTICE("Hamming Distance Debug: %ld\n", hamm_distance_debug);

	if(0 == hamm_distance_debug)
	{
		best_hamm_distance_code = 0;
		best_hamm_distance_bit = 0;
		
		memcpy(decoded_codeword, tmp_codeword, sizeof(unsigned char) * CODEWORD_LEN);
#if (1 == SYS_ENC)				
		memcpy(decoded_message, (tmp_codeword + (CODEWORD_LEN - MESSAGE_LEN)), sizeof(unsigned char) * MESSAGE_LEN);
#else
		memcpy(decoded_message, msg, sizeof(unsigned char) * MESSAGE_LEN);
#endif

		if(1 == decoding_ok_flag)
		{
			decoding_ok_flag = 2;
			DEBUG_NOTICE("decoding_ok_flag = 2!\n");
		}
		else
		{
			DEBUG_NOTICE("Strage Err: %d %d\n", decoding_ok_flag, hamm_distance_debug);
		}
		DEBUG_NOTICE("Match!\n");
	}

	DEBUG_NOTICE("Strage Test: %d %d\n", decoding_ok_flag, hamm_distance_debug);
#endif

#if 0
	/*special test*/
	unsigned char diff_cnt = 0;
	for(i = 0; i < MESSAGE_LEN; i++)
	{
		if(msg[i] != message_polynomial[i])
		{
			diff_cnt = diff_cnt + 1;
			break;
		}
	}
	if(0 == diff_cnt)
	{
		best_hamm_distance_code = 0;
		best_hamm_distance_bit = 0;
		
		memcpy(decoded_codeword, tmp_decoded_codeword, sizeof(unsigned char) * CODEWORD_LEN);
#if (1 == SYS_ENC)				
		memcpy(decoded_message, (tmp_decoded_codeword + (CODEWORD_LEN - MESSAGE_LEN)), sizeof(unsigned char) * MESSAGE_LEN);
#else
		memcpy(decoded_message, msg, sizeof(unsigned char) * MESSAGE_LEN);
#endif
		hamm_distance_debug = 0;

		if(1 == decoding_ok_flag)
		{
			decoding_ok_flag = 2;
		}
	}
#endif

	return 0;
}

int dfs_rr_recur(unsigned char *g_c_q,
					unsigned char *g_c_0_y,
					long long l)
{
	long long i = 0, j = 0;

	DEBUG_NOTICE("dfs_rr_recur: %ld\n", l);

	if(MESSAGE_LEN <= l)
	{
#if (0 == RE_ENCODING)		
		if(0xFF == g_term_x_0_cal_recur(g_c_q))
		{
			DEBUG_NOTICE("Message Found\n");
			check_rr_decoded_result_recur(tmp_message);

			return 1;
		}
		else
		{
			DEBUG_NOTICE("Decoding Fail\n");

			return 0;
		}
#else

#if (CFG_RR_MODE == CONV_RE_ENC_SYS)
		unsigned char tmp_cw[CODEWORD_LEN];
		evaluation_encoding_v2(tmp_message, tmp_cw);
		for(i = 0; i < CODEWORD_LEN; i++)
		{
			tmp_codeword[i] = gf_add(tmp_cw[i], phi[i]);
			DEBUG_NOTICE("cw_get: %ld | %x | %x\n",
						 i,
				         tmp_cw[i],
				         tmp_codeword[i]);
		}
#endif

#if (CFG_RR_MODE >= CONV_RE_ENC)
		for(i = 0; i < MESSAGE_LEN; i++)
		{
			tmp_message[i] = gf_add(tmp_message[i], H_msg[i]);
			DEBUG_NOTICE("msg_get: %ld | %x\n",
						 i,
				         tmp_message[i]);
		}
#endif

		check_rr_decoded_result_recur(tmp_message);

		return 1;
#endif
	}

#if (1 == RE_ENCODING)
#if (CFG_RR_MODE == BMA_RR)
	if(SYN_LEN <= l)
	{
		check_rr_decoded_result_recur(tmp_message);

		return 1;
	}
#endif	
#endif

	long long is_root = 0;
	unsigned char root = 0xFF;

#if (1 == DYNAMIC_MEM)
	unsigned char *g_c_q_new;
	g_c_q_new = (unsigned char*)malloc(sizeof(unsigned char) * (term_size_x * term_size_y));
#else
	unsigned char g_c_q_new[term_size_x * term_size_y];
#endif

	for(i = 0; i < GF_FIELD; i++)//test roots
	{
		memcpy(g_c_q_new, g_c_q, sizeof(unsigned char) * (term_size_x * term_size_y));
		g_term_0_y_cal_recur(g_c_q_new, g_c_0_y);

		is_root = chien_searching_for_g_0_y_recur(g_c_0_y, power_polynomial_table[i][0]);
		if(1 == is_root)
		{
			DEBUG_INFO("root0: %ld %ld %x\n", l, i, is_root);
			
			root = power_polynomial_table[i][0];
			tmp_message[l] = root;

			DEBUG_NOTICE("root0.5: %ld %ld %x\n", l, i, root);
			
			g_term_new_gen_recur(g_c_q_new, root);

			DEBUG_INFO("root1: %ld %ld %x\n", l, i, root);

			dfs_rr_recur(g_c_q_new,
						  g_c_0_y,
						  l + 1);
			DEBUG_INFO("root2: %ld %ld %x\n", 0, i, root);
		}
	}

#if (1 == DYNAMIC_MEM)
	free(g_c_q_new);
	g_c_q_new = NULL;
#endif	
	
	return 0;
}

int rr_factorization_recur()
{
	best_hamm_distance_code = 0x7FFF;
	best_hamm_distance_bit = 0x7FFF;
	
	long long i = 0, j = 0;
	long long is_root = 0;
	unsigned char root = 0xFF;

#if (1 == DYNAMIC_MEM)
	unsigned char *g_c_q, *g_c_0_y, *g_c_q_origin;
	g_c_q = (unsigned char*)malloc(sizeof(unsigned char) * (term_size_x * term_size_y));
	g_c_0_y = (unsigned char*)malloc(sizeof(unsigned char) * (term_size_x * term_size_y));
	g_c_q_origin = (unsigned char*)malloc(sizeof(unsigned char) * (term_size_x * term_size_y));
#else
	unsigned char g_c_q[term_size_x * term_size_y], g_c_0_y[term_size_x * term_size_y];
#endif

	memcpy(g_c_q_origin, g_term_c_p[g_term_phase][0], sizeof(unsigned char) * (term_size_x * term_size_y));

	for(i = 0; i < GF_FIELD; i++)//test roots
	{
		//DEBUG_INFO("root00: %ld %ld %x\n", 0, i, g_term_c_p[g_term_phase][0][0]);
		memcpy(g_c_q, g_c_q_origin, sizeof(unsigned char) * (term_size_x * term_size_y));
		g_term_0_y_cal_recur(g_c_q, g_c_0_y);

		is_root = chien_searching_for_g_0_y_recur(g_c_0_y, power_polynomial_table[i][0]);
		if(1 == is_root)
		{
			root = power_polynomial_table[i][0];
			tmp_message[0] = root;
			g_term_new_gen_recur(g_c_q, root);

			DEBUG_INFO("root: %ld %ld %x\n", 0, i, root);
			
			dfs_rr_recur(g_c_q,
						  g_c_0_y,
						  1);
			DEBUG_INFO("root11: %ld %ld %x\n", 0, i, root);
		}
	}

#if (1 == DYNAMIC_MEM)
	free(g_c_q);
	g_c_q = NULL;
	free(g_c_0_y);
	g_c_0_y = NULL;
	free(g_c_q_origin);
	g_c_q_origin = NULL;
#endif

	return 0;
}

float euc_distance_code_cal(unsigned char *a,
								   float **b,
								   long long len)
{
	float euc_distance = 0;

	long long i = 0;
	long long symbol_num = CODEWORD_LEN * GF_Q * BITS_PER_SYMBOL_BPSK;
	float **a_mod;
	a_mod = (float**)malloc(sizeof(float*) * symbol_num);
	for (i = 0; i < symbol_num; i++)
	{
		a_mod[i] = (float*)malloc(sizeof(float) * 2);
	}

	bpsk_mod(a,
			 len,
			 a_mod,
			 symbol_num);

	for(i = 0; i < symbol_num; i++)
	{
		euc_distance = euc_distance + abs(a_mod[i][0] - b[i][0])
									+ abs(a_mod[i][1] - b[i][1]);
	}

	for (i = 0; i < symbol_num; i++)
	{
  		free(a_mod[i]);
		a_mod[i] = NULL;
  	}
	free(a_mod);
	a_mod = NULL;

	//DEBUG_IMPOTANT("Euc. Distance Test: %d\n", euc_distance);

	return euc_distance;
}

long long hamm_distance_code_cal(unsigned char *a,
									  unsigned char *b,
									  long long len)
{
	long long hamm_distance = 0;

	long long i = 0;

	for(i = 0; i < len; i++)
	{
		if(a[i] != b[i])
		{
			//DEBUG_NOTICE("hamm_distance_cal: %d %d\n", a[i], b[i]);
			hamm_distance = hamm_distance + 1;
		}
	}

	//DEBUG_IMPOTANT("Hamming Distance Test: %d\n", hamm_distance);

	return hamm_distance;
}

long long hamm_distance_bit_cal(unsigned char *a,
									  unsigned char *b,
									  long long len)
{
	long long hamm_distance_bit = 0;

	long long i = 0, j = 0;
	unsigned char tmp_a = 0, tmp_b = 0;

	for(i = 0; i < len; i++)
	{
		if(a[i] != b[i])
		{
			for(j = 0; j < GF_Q; j++)
			{
				/*notice these indexes, 0xFF + 0x1 = 0, ..., 0x6 + 0x1 = 7*/
				tmp_a = (power_polynomial_table[a[i] + 0x1][1] >> j) & 0x1;
				tmp_b = (power_polynomial_table[b[i] + 0x1][1] >> j) & 0x1;

				if(tmp_a != tmp_b)
				{
					hamm_distance_bit = hamm_distance_bit + 1;
				}
			}
		}
	}

	//DEBUG_IMPOTANT("Hamming Distance Test: %d\n", hamm_distance);

	return hamm_distance_bit;
}

#if (1 == RE_ENCODING)
#if (CFG_RR_MODE == FAST_RR_M1)
int fast_msg_get()
{
	long long i = 0, j = 0;
	
	unsigned char q0[CODEWORD_LEN], q1[CODEWORD_LEN];
	unsigned char q0_dev[CODEWORD_LEN], q1_dev[CODEWORD_LEN], v_dev[MESSAGE_LEN + 1];
	unsigned char rec_dir_cw[CODEWORD_LEN];
	unsigned char tmp_v[term_size_x * term_size_y];
	unsigned char tmp_q0[term_size_x * term_size_y];
	unsigned char tmp_q1[term_size_x * term_size_y];
	unsigned char v_val = 0xFF, q1_val = 0xFF, q0_val = 0xFF;

	memset(q0, 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
	memset(q1, 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
	memset(q0_dev, 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
	memset(q1_dev, 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
	memset(v_dev, 0xFF, sizeof(unsigned char) * (MESSAGE_LEN + 1));
	memset(rec_dir_cw, 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
	memset(tmp_v, 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));
	memset(tmp_q0, 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));
	memset(tmp_q1, 0xFF, sizeof(unsigned char) * (term_size_x * term_size_y));

	for(i = 0; i < (term_size_x * term_size_y); i++)
	{
		if((0xFF != g_term_c_p[g_term_phase][0][i])
			&& (0 == g_term_y[i]))
		{
			tmp_q0[i] = g_term_c_p[g_term_phase][0][i];
		}
	}

	for(i = 0; i < (term_size_x * term_size_y); i++)
	{
		if((0xFF != g_term_c_p[g_term_phase][0][i])
			&& (0 != g_term_y[i]))
		{
			tmp_q1[i] = g_term_c_p[g_term_phase][0][i];
		}
	}

	for(i = 0; i < (term_size_x * term_size_y); i++)
	{
		if(0xFF != tmp_q0[i])
		{
			DEBUG_NOTICE("q0: %d %d| %x\n", g_term_x[i], g_term_y[i], tmp_q0[i]);
			q0[g_term_x[i]] = tmp_q0[i];
		}
	}

	for(i = 0; i < (term_size_x * term_size_y); i++)
	{
		if(0xFF != tmp_q1[i])
		{
			DEBUG_NOTICE("q1: %d %d| %x\n", g_term_x[i], g_term_y[i], tmp_q1[i]);
			q1[g_term_x[i]] = tmp_q1[i];
		}
	}

	for(i = 0; i < CODEWORD_LEN; i++)
	{
		DEBUG_NOTICE("q: %ld | %x %x\n", i, q0[i], q1[i]);
	}

	for(i = 0; i < CODEWORD_LEN; i++)
	{
		q0_val = poly_eva(q0,
			              CODEWORD_LEN,
			              power_polynomial_table[i + 1][0]);
		v_val = poly_eva(v,
			             (MESSAGE_LEN + 1),
			             power_polynomial_table[i + 1][0]);
		q1_val = poly_eva(q1,
		                  CODEWORD_LEN,
		                  power_polynomial_table[i + 1][0]);
		if(0xFF != q1_val)
		{
			rec_dir_cw[i] = gf_div(gf_multp(q0_val, v_val),
								   q1_val);
		}
		else//there are some problems now
		{
			for(j = 0; j < CODEWORD_LEN; j++)
			{
				if(0 != (j % 2))
				{
					q1_dev[j - 1] = q1[j];
				}
				else
				{
					q1_dev[j - 1] = 0xFF;
				}
			}
			q1_val = poly_eva(q1_dev,
			                  CODEWORD_LEN,
			              	  power_polynomial_table[i + 1][0]);
			
			if(0xFF == v_val)
			{
				for(j = 1; j < (MESSAGE_LEN + 1); j++)
				{
					if(0 != (j % 2))
					{
						v_dev[j - 1] = v[j];
					}
					DEBUG_NOTICE("v_dev: %ld | %x\n", j - 1, v_dev[j - 1]);
				}

				v_val = poly_eva(v_dev,
			             		 (MESSAGE_LEN + 1),
			             		 power_polynomial_table[i + 1][0]);

				rec_dir_cw[i] = gf_div(gf_multp(q0_val, v_val),
								       q1_val);
			}

			if(0xFF == q0_val)
			{
				for(j = 1; j < (MESSAGE_LEN + 1); j++)
				{
					if(0 != (j % 2))
					{
						q0_dev[j - 1] = q0[j];
					}
					DEBUG_NOTICE("q0_dev: %ld | %x\n", j - 1, q0_dev[j - 1]);
				}

				q0_val = poly_eva(q0_dev,
			             		 CODEWORD_LEN,
			             		 power_polynomial_table[i + 1][0]);

				rec_dir_cw[i] = gf_div(gf_multp(q0_val, v_val),
								       q1_val);
			}
		}

		decoded_codeword[i] = gf_add(rec_dir_cw[i], phi[i]);

		DEBUG_NOTICE("rec_dir_cw: %d | %x*%x/%x=%x | %x\n",
			         i,
			         v_val,
			         q0_val,
			         q1_val,
			         rec_dir_cw[i],
			         decoded_codeword[i]);
	}

	memcpy(decoded_message, decoded_codeword + (CODEWORD_LEN - MESSAGE_LEN), sizeof(unsigned char) * MESSAGE_LEN);

	return 0;
}
#endif
#endif

#if (1 == DYNAMIC_TERM)
int term_size_adjust()
{
	long long i = 0, j = 0, k = 0;

	DEBUG_INFO("term_size_adjust: %ld %ld | %ld %ld\n",
		      max_dx * DYNAMIC_TERM_X,
		      term_size_x,
		      max_dy * DYNAMIC_TERM_Y,
		      term_size_y);

#if 0
	if((((max_dx * DYNAMIC_TERM_X - term_size_x) <= 2)
			&& ((max_dx * DYNAMIC_TERM_X) >= term_size_x))
		|| (((term_size_x - max_dx * DYNAMIC_TERM_X) <= 2)
			&& ((max_dx * DYNAMIC_TERM_X) < term_size_x)))
#else
	if((max_dx * DYNAMIC_TERM_X - max_dx) <= 2)
#endif
	{
		term_size_x = max_dx + 5;
	}
	else
	{
		term_size_x = max_dx * DYNAMIC_TERM_X + 5;
	}
	//term_size_x = 968;
#if 0	
	if((((max_dy * DYNAMIC_TERM_Y - term_size_y) <= 2)
			&& ((max_dy * DYNAMIC_TERM_Y) >= term_size_y))
		|| (((term_size_y - max_dy * DYNAMIC_TERM_Y) <= 2)
			&& ((max_dy * DYNAMIC_TERM_Y) < term_size_y)))
#else
	if((max_dy * DYNAMIC_TERM_Y - term_size_y) <= 2)
#endif
	{
		term_size_y = max_dy + 2;
	}
	else
	{
		term_size_y = max_dy * DYNAMIC_TERM_Y + 2;
	}

	free(g_term_x);
	g_term_x = NULL;
	free(g_term_y);
	g_term_y = NULL;
	g_term_x = (long long*)malloc(sizeof(long long) * (term_size_x * term_size_y));
	g_term_y = (long long*)malloc(sizeof(long long) * (term_size_x * term_size_y));

	for(i = 0; i < term_size_x; i++)
	{
		for(j = 0; j < term_size_y; j++)
		{
			g_term_x[k] = i;
			g_term_y[k] = j;
			k++;
		}
	}
	
	return 0;
}
#endif

int as_decoding()
{
	long long i = 0;
	int ml_result = 0;
#if (1 == CFG_DEBUG_IMPOTANT)	
	DEBUG_IMPOTANT("Received:\n");
	for(i = 0; i < CODEWORD_LEN; i++)
	{
		DEBUG_IMPOTANT("%x ", received_polynomial[i]);
	}
	DEBUG_IMPOTANT("\n");
#endif

	best_tst_vct_diff = CODEWORD_LEN;
	processed_tst_vct_num = 0;
	
	g_decoded_cnt = 0;
	
	replace_cnt = 0;

	clock_t start, stop;
	float runtime;
	start = clock();

	memset(decoded_codeword, 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
	memset(decoded_message, 0xFF, sizeof(unsigned char) * MESSAGE_LEN);

	stop = clock();
	runtime = (stop - start) / 1000.0000;
	//DEBUG_SYS("Time1 %fs\n", runtime);

	g_term_init();

	stop = clock();
	runtime = (stop - start) / 1000.0000;
	//DEBUG_SYS("Time2 %fs\n", runtime);

#if 0//for lcc interpolation test, not care about interpolating order
	unsigned char tmp = received_polynomial[0];
	received_polynomial[1] = received_polynomial[CODEWORD_LEN - 2];
	received_polynomial[CODEWORD_LEN - 2] = tmp;
	tmp = received_polynomial[1];
	received_polynomial[1] = received_polynomial[CODEWORD_LEN - 3];
	received_polynomial[CODEWORD_LEN - 3] = tmp;
#endif

	uncommon_place_init();
	intrplt_seq_init();

#if (0 == CFG_BR)

#if (1 == CFG_PHI_FAST_SKIP)

	if(1 == MLcriterion(phi))
	{
		memcpy(decoded_codeword, phi, sizeof(unsigned char) * CODEWORD_LEN);
		memcpy(decoded_message, decoded_codeword + (CODEWORD_LEN - MESSAGE_LEN), sizeof(unsigned char) * MESSAGE_LEN);
		
#if 1
		stop_t = clock();
		//runtime_t = runtime_t + (stop_t - start_t) / 1000.0000;
#endif
		
		
		return 0;
	}
#endif

	koetter_interpolation();
#endif

#if (1 == CFG_BR)
	interpolation_init();
#endif
	uncommon_interpolation_init();

#if (1 == CFG_NEW_TST_VCT)
	new_tst_vct_init();
#endif

#if (1 == CFG_ADAPTIVE_PARALLEL)
	long long batch_size = pow_val;
	long long round_size = pow_val;
#else
	long long batch_size = pow_val / PARALLEL_BATCH_NUM;
	long long round_size = PARALLEL_BATCH_NUM;
#endif
	long long decoded_cnt = 0, decoded_round_cnt = 0, last_round = 0;

	long long latency_worst_case_add = 0, latency_worst_case_mul = 0;
	long long add_prev = add_cnt, mul_prev = mul_cnt + div_cnt;
	long long add_prev_round = add_cnt, mul_prev_round = mul_cnt + div_cnt;

#if (1 == CFG_BR)
	tst_vct_trans_init();
#if (1 == CFG_PHI_FAST_SKIP)

	if((1 == MLcriterion(phi))
		|| (1 == phi_compare_fast_skip(0)))
	{
		memcpy(uncommon_decoded_codeword[0], phi, sizeof(unsigned char) * CODEWORD_LEN);
		check_lcc_result();
		
		tst_vct_trans_exit();
		uncommon_interpolation_exit();
		
#if (1 == CFG_NEW_TST_VCT)
		new_tst_vct_exit();
#endif		
#if 0
		stop_t = clock();
		runtime_t = runtime_t + (stop_t - start_t) / 1000.0000;
#endif
		return 0;
	}
#endif	
	br_cmm_interpolation();

#if (1 == CFG_NEW_TST_VCT)
	new_tst_vct_trans_init();
#endif
#endif

#if (1 == CFG_ADAPTIVE_PARALLEL)
	adaptive_parallel_init();
#endif	

#if (0 == CFG_ADAPTIVE_PARALLEL)
	tst_vct_seq_cal();
#endif	

#if (CFG_RR_MODE == FAST_RR_M1)
	g_v_val_cal();
#endif

	long long k = 0, l = 0;
	int tst_skip_cnt = CODEWORD_LEN;
#if (1 == CFG_PARTIALLY_PARALLEL)
	//gf_count_reset();
#endif
#if (1 == CFG_STORE_PARALEL)
	store_place = -1;
#endif
	
	stop_t = clock();
	//runtime_t = runtime_t + (stop_t - start_t) / 1000.0000;
	//start_t = clock();

	for(l = 0; l < batch_size; l++)//round_idx
	{
		latency_worst_case_add = 0;
		latency_worst_case_mul = 0;
	
		decoded_round_cnt = decoded_cnt;

#if (1 == CFG_RE_ARRANGE_TST_VCT)
		decoded_round_cnt = processed_tst_vct_num;
		//if(2 > l)
		{
			//rearrange_tst_vct(decoded_round_cnt, l);
			rearrange_tst_vct_old(decoded_round_cnt, l);
		}
#endif

		for(k = 0; k < round_size; k++)//batch_idx
		{

#if 1//(1 == CFG_ADAPTIVE_PARALLEL)
			if(-1 == tst_vct_seq[k][l])
			{
				continue;
			}
#endif
			last_round = l;
			DEBUG_INFO("tst_vct_seq_check: %d %d %d\n", k, l, tst_vct_seq[k][l]);

			if(0 == k)
			{
				tv_round_clock_base_prev = 1;
				tv_round_clock_base = tst_vct_seq[k][l];
			}
			else
			{
				tv_round_clock_base_prev = 0;
			}
#if (1 == CFG_ADAPTIVE_PARALLEL)
			decoded_tst_vct_seq[decoded_cnt] = tst_vct_seq[k][l];
#else
			decoded_tst_vct_seq[k * batch_size + l] = tst_vct_seq[k][l];
#endif
			decoded_cnt++;
			adaptive_vct_seq_mark[tst_vct_seq[k][l]] = 2;
			processed_tst_vct_num++;
			DEBUG_INFO("processed_tst_vct_dec: %ld %ld\n", processed_tst_vct_num, tst_vct_seq[k][l]);
#if (1 == CFG_RE_ARRANGE_TST_VCT)			
			//adaptive_vct_seq_mark[tst_vct_seq[k][l]] = 1;
#endif			

#if (1 == CFG_PARTIALLY_PARALLEL)
#if (1 == CFG_PARALLEL_FAST_SKIP)
#if (1 == CFG_ADAPTIVE_PARALLEL)
			tst_skip_cnt = fast_skip_tst_vct(tst_vct_seq[k][l], decoded_round_cnt);
#else
			tst_skip_cnt = fast_skip_tst_vct(tst_vct_seq[k][l], l * PARALLEL_BATCH_NUM);
#endif
			if(((CODEWORD_LEN - MESSAGE_LEN) / 2) >= tst_skip_cnt)
			{
				DEBUG_INFO("tst_vct_skip: %d %d %d\n",
				           tst_vct_seq[k][l],
				           (l / PARALLEL_BATCH_NUM) * PARALLEL_BATCH_NUM,
				           tst_skip_cnt);

				//if(l == (batch_size - 1))
				{
#if (0 == CFG_ADAPTIVE_PARALLEL)				
					gf_partially_parallel_cnt(k);
#endif					
					//DEBUG_SYS("parallel_cnt: %d %d\n", batch_idx, l);
				}

				skip_hist[tst_vct_seq[k][l]]++;

				continue;
			}
			DEBUG_INFO("tst_vct_continue: %d %d\n", l, tst_skip_cnt);
#endif
#endif

#if (1 == CFG_FAST_SKIP_TST_VCT)
			tst_skip_cnt = fast_skip_tst_vct(tst_vct_seq[k][l], l * PARALLEL_BATCH_NUM);
			if(((CODEWORD_LEN - MESSAGE_LEN) / 2) >= tst_skip_cnt)
			{
				DEBUG_INFO("tst_vct_skip: %d %d\n", l, tst_skip_cnt);
				skip_hist[tst_vct_seq[k][l]]++;
				continue;
			}
			DEBUG_INFO("tst_vct_continue: %d %d\n", l, tst_skip_cnt);
#endif		

			DEBUG_INFO("tst_vct_seq_int: %d %d %d\n", k, l, tst_vct_seq[k][l]);

#if (0 == CFG_BR)
			//start_t = clock();
			uncommon_interpolation(tst_vct_seq[k][l]);
			//stop_t = clock();
			//runtime_t = runtime_t + (stop_t - start_t) / 1000.0000;
#if (CFG_RR_MODE == FAST_RR_M1)
			//gf_count_switch(1);
			uncommon_fast_msg_get(tst_vct_seq[k][l]);
			//gf_count_switch(0);
#endif

#if (CFG_RR_MODE == BMA_RR)
			//fast_err_in_r_get(tst_vct_seq[k][l]);
#if (1 == CFG_Q0_FAST_SKIP)			
			if(1 == fast_root_finding_skip(tst_vct_seq[k][l]))
			{
				continue;
			}
#endif
			uncommon_rr_factorization_recur(tst_vct_seq[k][l]);
			uncommon_recover_codeword(tst_vct_seq[k][l]);
#endif

#if (CFG_RR_MODE == CONV_RE_ENC_SYS)
#if (1 == CFG_Q0_FAST_SKIP)			
			if(1 == fast_root_finding_skip(tst_vct_seq[k][l]))
			{
				continue;
			}
#endif
			uncommon_rr_factorization_recur(tst_vct_seq[k][l]);
			uncommon_recover_codeword(tst_vct_seq[k][l]);
#endif

#endif//CFG_BR

#if (1 == CFG_BR)
			br_uncmm_interpolation(tst_vct_seq[k][l]);
#endif

#if (1 == CFG_PARTIALLY_PARALLEL)
			//if(l == (batch_size - 1))//???
			{
#if (0 == CFG_ADAPTIVE_PARALLEL)			
				gf_partially_parallel_cnt(k);
				//DEBUG_SYS("parallel_cnt: %d %d\n", batch_idx, l);
#endif				
			}
#endif
			if(latency_worst_case_add < (add_cnt - add_prev))
			{
				latency_worst_case_add = add_cnt - add_prev;
			}
			if(latency_worst_case_mul < ((mul_cnt + div_cnt) - mul_prev))
			{
				latency_worst_case_mul = (mul_cnt + div_cnt) - mul_prev;
			}
			add_prev = add_cnt;
			mul_prev = mul_cnt + div_cnt;
			
			DEBUG_INFO("a_add: %ld %f %f\n",
			          k,
			          (double)(add_cnt - add_prev_round) / (double)(1),
			          (double)latency_worst_case_add / (double)(1));
			DEBUG_INFO("a_mul: %ld %f %f\n",
			          k,
			          (double)(mul_cnt + div_cnt - mul_prev_round) / (double)(1),
			          (double)latency_worst_case_mul / (double)(1));
		}

		cmplx_per_round_add[l] = cmplx_per_round_add[l] + add_cnt - add_prev_round;
		cmplx_per_round_mul[l] = cmplx_per_round_mul[l] + mul_cnt + div_cnt - mul_prev_round;
		add_prev_round = add_cnt;
		mul_prev_round = mul_cnt + div_cnt;
		
		latency_per_round_add[l] = latency_per_round_add[l] + latency_worst_case_add;
		latency_per_round_mul[l] = latency_per_round_mul[l] + latency_worst_case_mul;
		
		DEBUG_INFO("b_add: %ld %f %f\n",
		          l,
		          (double)cmplx_per_round_add[l] / (double)(1),
		          (double)latency_per_round_add[l] / (double)(1));
		DEBUG_INFO("b_mul: %ld %f %f\n",
		          l,
		          (double)cmplx_per_round_mul[l] / (double)(1),
		          (double)latency_per_round_mul[l] / (double)(1));
		          
#if (1 == CFG_PRG_DECODING)
		for(k = 0; k < round_size; k++)
		{
#if 1//(1 == CFG_ADAPTIVE_PARALLEL)		
			if(-1 == tst_vct_seq[k][l])
			{
				continue;
			}
#endif			

			ml_result = MLcriterion(uncommon_decoded_codeword[tst_vct_seq[k][l]]);
			if(1 == ml_result)
			{
				ml_tst_vct_recv_diff = 0;
				ml_tst_vct_enc_diff = 0;
				for(i = 0; i < CODEWORD_LEN; i++)
				{
					if(uncommon_decoded_codeword[tst_vct_seq[k][l]][i] != received_polynomial[i])
					{
						ml_tst_vct_recv_diff++;
					}
					if(uncommon_decoded_codeword[0][i] != received_polynomial[i])
					{
						ml_tst_vct_enc_diff++;
					}
				}

				if(0 != last_round)
				{
					DEBUG_INFO("ml_diff: %ld %ld %ld %f %f\n",
							  ml_tst_vct_recv_diff,
							  ml_tst_vct_enc_diff,
							  last_round,
							  tst_vct_rel[0],
							  tst_vct_rel[tst_vct_seq[k][l]]);
					//DEBUG_SYS("g_time_cnt: %ld\n", g_time_cnt);
				}

				DEBUG_INFO("ml_result: %ld | %d %d\n", l, ml_result, tst_vct_seq[k][l]);
				break;
			}
		}
		if(1 == ml_result)
		{
			pgd_hist[tst_vct_seq[k][l]]++;
			break;
		}
#endif
	}

#if 0//(1 == CFG_BR)
	br_test();
#endif

	check_lcc_result();

#if (1 == CFG_PRG_DECODING)		
	if(0 == ml_result)
	{
		DEBUG_INFO("decoded_cnt: %ld\n", decoded_cnt);
		DEBUG_INFO("No early termination for PRG_DECODING\n");
		if((decoded_cnt != pow_val)
			&& (1000 > chnl_rel_order[YITA]))
		{
			DEBUG_INFO("chnl_rel_order_free: %ld %f %ld\n",
					  decoded_cnt,
					  chnl_rel_order[YITA],
		              chnl_rel_order_idx[YITA]);
		}
		if((pow_val + 1) > g_decoded_cnt)
		{
			g_decoded_cnt = decoded_cnt;
		}
#if 0
		return 0;
#endif

		ml_tst_vct_recv_diff = 0;
		ml_tst_vct_enc_diff = 0;
		for(i = 0; i < CODEWORD_LEN; i++)
		{
			if(decoded_codeword[i] != encoded_polynomial[i])
			{
				ml_tst_vct_enc_diff++;
			}
			if(decoded_codeword[i] != received_polynomial[i])
			{
				ml_tst_vct_recv_diff++;
			}
		}

		if(0 == ml_tst_vct_enc_diff)
		{
			DEBUG_INFO("no_ml_diff: %ld %ld\n",
				  	  ml_tst_vct_recv_diff,
				  	  ml_tst_vct_enc_diff);
		}
	}
#endif
	
#if (1 == CFG_BR)
	tst_vct_trans_exit();
	
#if (1 == CFG_NEW_TST_VCT)
	new_tst_vct_trans_exit();
#endif	
#endif

	uncommon_interpolation_exit();
	
#if (1 == CFG_NEW_TST_VCT)
	new_tst_vct_exit();
#endif	

#if (1 == CFG_ADAPTIVE_PARALLEL)
	adaptive_parallel_exit();
#endif	

#if 1//(1 == CFG_ADAPTIVE_PARALLEL)
	round_hist[last_round]++;
#else
	round_hist[l]++;
#endif	
	DEBUG_INFO("round_hist: %ld %ld %ld\n", l, last_round, round_hist[l]);

	stop = clock();
	runtime = (stop - start) / 1000.0000;
	//DEBUG_SYS("Time3 %fs\n", runtime);

#if 0

#if (CFG_RR_MODE == FAST_RR_M1)
	fast_msg_get();
#else

#if (1 == RECUR_RR)
	rr_factorization_recur();
#else
	rr_factorization();

	stop = clock();
	runtime = (stop - start) / 1000.0000;
	//DEBUG_SYS("Time4 %fs\n", runtime);

	check_rr_decoded_result();
#endif
	stop = clock();
	runtime = (stop - start) / 1000.0000;
	//DEBUG_SYS("Time5 %fs\n", runtime);

#if (CFG_RR_MODE == BMA_RR)
	recover_codeword();
#endif

#endif

#endif

#if (1 == DYNAMIC_TERM)
	term_size_adjust();

	stop = clock();
	runtime = (stop - start) / 1000.0000;
	//DEBUG_SYS("Time6 %fs\n", runtime);
#endif

	//stop_t = clock();
	//runtime_t = runtime_t + (stop_t - start_t) / 1000.0000;

	return 0;
}
