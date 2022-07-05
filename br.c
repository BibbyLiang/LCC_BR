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

#define B_MATRIX_SIZE	(S_MUL + 1)

unsigned char g_cmm_poly[CODEWORD_LEN + 1];
unsigned char g_poly[CODEWORD_LEN + 1];
unsigned char r_poly[CODEWORD_LEN + 1];
unsigned char t_poly[CODEWORD_LEN][CODEWORD_LEN + 1];
unsigned char b_matrix[B_MATRIX_SIZE][B_MATRIX_SIZE][CODEWORD_LEN + 2];//0 -> x^(-1)
unsigned char a_matrix[B_MATRIX_SIZE][B_MATRIX_SIZE][CODEWORD_LEN + 2];//0 -> x^(-1)
unsigned char a_cmm_matrix[B_MATRIX_SIZE][B_MATRIX_SIZE][CODEWORD_LEN + 2];

long long lp[B_MATRIX_SIZE];
long long ld[B_MATRIX_SIZE];

unsigned char t_div[CODEWORD_LEN];
unsigned char t_wave_poly[CODEWORD_LEN][CODEWORD_LEN + 1];

unsigned char **tst_vct_trans;//size: (2^yita) * codewordlen
unsigned char *tst_vct_cmm_trans;

unsigned char **gamma_poly;

int t_poly_construct(unsigned char locator_j, unsigned char *L)
{
	DEBUG_NOTICE("%s: %x\n", __func__, locator_j);
	long long i = 0, j = 0;
	unsigned char v_tmp_1[CODEWORD_LEN + 1], v_tmp_2[CODEWORD_LEN + 1];
	unsigned char tmp_div = 0, tmp_inv = 0xFF;

	memset(L, 0xFF, sizeof(unsigned char) * (CODEWORD_LEN + 1));
	L[0] = 0;

	for(i = 1; i < GF_FIELD; i++)
	{
		if(power_polynomial_table[i][0] == locator_j)
		{
			continue;
		}
		
		memset(v_tmp_1, 0xFF, sizeof(unsigned char) * (CODEWORD_LEN + 1));
		memset(v_tmp_2, 0xFF, sizeof(unsigned char) * (CODEWORD_LEN + 1));

		for(j = 0; j < CODEWORD_LEN; j++)
		{
			v_tmp_1[j + 1] = L[j];//increase degree because of x term
			//DEBUG_NOTICE("v_tmp_1: %d | %x\n", j + 1, v_tmp_1[j + 1]);

			if(0x0 == L[j])
			{
				v_tmp_2[j] = power_polynomial_table[i][0];
				//DEBUG_NOTICE("v_tmp_2: %d | %x=%x*%x\n", j, v_tmp_2[j], L[j], power_polynomial_table[i][0]);
				continue;
			}
			if(0xFF != L[j])
			{
				v_tmp_2[j] = gf_multp(L[j], power_polynomial_table[i][0]);//calculation of a_i term
			}
			//DEBUG_NOTICE("v_tmp_2: %d | %x=%x*%x\n", j, v_tmp_2[j], L[j], power_polynomial_table[i][0]);
		}

		for(j = 0; j < (CODEWORD_LEN + 1); j++)
		{
			if(0xFF == v_tmp_1[j])
			{
				L[j]= v_tmp_2[j];
				//DEBUG_NOTICE("v_tmp: %d %d | %x\n", i, j, L[j]);
				continue;
			}
			if(0xFF == v_tmp_2[j])
			{
				L[j]= v_tmp_1[j];
				//DEBUG_NOTICE("v_tmp: %d %d | %x\n", i, j, L[j]);
				continue;
			}
			L[j] = gf_add(v_tmp_1[j], v_tmp_2[j]);//add 2 parts
			//DEBUG_NOTICE("v_tmp: %d %d | %x\n", i, j, L[j]);
		}
	}

	for(i = 1; i < GF_FIELD; i++)
	{
		if(power_polynomial_table[i][0] == locator_j)
		{
			continue;
		}

		tmp_inv = gf_div(0x0, gf_add(locator_j, power_polynomial_table[i][0]));
		//DEBUG_NOTICE("tmp_inv: %d | %x\n", i, tmp_inv);
		tmp_div = gf_multp(tmp_div, tmp_inv);
		//DEBUG_NOTICE("tmp_div: %d | %x\n", i, tmp_div);
	}
	t_div[locator_j] = tmp_div;//for mul
	DEBUG_NOTICE("t_div: %d %x\n", locator_j, t_div[locator_j]);

	for(i = 0; i < (CODEWORD_LEN + 1); i++)
	{
		if(0x0 == L[i])
		{
			L[i] = tmp_div;
			DEBUG_NOTICE("L: %d %d | %x\n", locator_j, i, L[i]);
			continue;
		}
		if(0x0 == tmp_div)
		{
			DEBUG_NOTICE("L: %d %d | %x\n", locator_j, i, L[i]);
			continue;
		}
	
		L[i] = gf_multp(L[i], tmp_div);
		DEBUG_NOTICE("L: %d %d | %x\n", locator_j, i, L[i]);
	}
	
	return 0;
}

int lagrange_poly_construct()
{
	DEBUG_NOTICE("%s\n", __func__);
	long long i = 0, j = 0;

	for(i = 1; i < GF_FIELD; i++)
	{
		t_poly_construct(power_polynomial_table[i][0], t_poly[i - 1]);
	}

	return 0;
}

int g_wave_poly_gen()
{
	long long i = 0, j = 0;
	unsigned char find_flag = 0;
	
	memset(g_poly, 0xFF, sizeof(unsigned char) * (CODEWORD_LEN + 1));

	for(j = 0; j < MESSAGE_LEN; j++)
	{
		if(0 == rel_group_seq[j])
		{
			find_flag = 1;
			break;
		}
	}
	if(1 != find_flag)
	{
		g_poly[0] = power_polynomial_table[1][0];
	}
	g_poly[1] = 0;
	unsigned char g_tmp_1[CODEWORD_LEN + 1], g_tmp_2[CODEWORD_LEN + 1];

	for(i = 1; i < (CODEWORD_LEN + 0); i++)
	{
		find_flag = 0;
		for(j = 0; j < MESSAGE_LEN; j++)
		{
			if(i == rel_group_seq[j])
			{
				find_flag = 1;
				break;
			}
		}
		if(1 == find_flag)
		{
			continue;
		}
	
		memset(g_tmp_1, 0xFF, sizeof(unsigned char) * (CODEWORD_LEN + 1));
		memset(g_tmp_2, 0xFF, sizeof(unsigned char) * (CODEWORD_LEN + 1));

		for(j = 0; j < (CODEWORD_LEN + 1); j++)
		{
			if(0 != j)//increase degree because of x term
			{
				g_tmp_1[j] = g_poly[j - 1];
				DEBUG_NOTICE("g_tmp_1: %d | %x\n", j, g_tmp_1[j]);
			}

			if(0xFF != g_poly[j])
			{
				g_tmp_2[j] = gf_multp(g_poly[j], power_polynomial_table[i + 1][0]);//calculation of a_i term
				DEBUG_NOTICE("g_tmp_2: %d | %x=%x*%x\n", j, g_tmp_2[j], g_poly[j], rel_group_seq[i + 1]);
			}
		}

		for(j = 0; j < (CODEWORD_LEN + 1); j++)
		{
			if(0xFF == g_tmp_1[j])
			{
				g_poly[j] = g_tmp_2[j];
			}
			else if(0xFF == g_tmp_2[j])
			{
				g_poly[j] = g_tmp_1[j];
			}
			else
			{
				g_poly[j] = gf_add(g_tmp_1[j], g_tmp_2[j]);//add 2 parts
			}
			DEBUG_NOTICE("g_tmp: %d | %x\n", j, g_poly[j]);
		}
	}

	for(i = 0; i < (CODEWORD_LEN + 1); i++)
	{
		DEBUG_NOTICE("g_poly: %d | %x\n", i, g_poly[i]);
	}
	//memcpy(g_cmm_poly, g_poly, sizeof(unsigned char) * (CODEWORD_LEN + 1));
}

int g_poly_gen()
{
	long long i = 0, j = 0;
	
	memset(g_poly, 0xFF, sizeof(unsigned char) * (CODEWORD_LEN + 1));
	
	g_poly[0] = power_polynomial_table[1][0];
	g_poly[1] = 0;
	unsigned char g_tmp_1[CODEWORD_LEN + 1], g_tmp_2[CODEWORD_LEN + 1];

	for(i = 1; i < (CODEWORD_LEN + 0); i++)
	{
		memset(g_tmp_1, 0xFF, sizeof(unsigned char) * (CODEWORD_LEN + 1));
		memset(g_tmp_2, 0xFF, sizeof(unsigned char) * (CODEWORD_LEN + 1));

		for(j = 0; j < (CODEWORD_LEN + 1); j++)
		{
			if(0 != j)//increase degree because of x term
			{
				g_tmp_1[j] = g_poly[j - 1];
				DEBUG_NOTICE("g_tmp_1: %d | %x\n", j, g_tmp_1[j]);
			}

			if(0xFF != g_poly[j])
			{
				g_tmp_2[j] = gf_multp(g_poly[j], power_polynomial_table[i + 1][0]);//calculation of a_i term
				DEBUG_NOTICE("g_tmp_2: %d | %x=%x*%x\n", j, g_tmp_2[j], g_poly[j], rel_group_seq[i + 1]);
			}
		}

		for(j = 0; j < (CODEWORD_LEN + 1); j++)
		{
			if(0xFF == g_tmp_1[j])
			{
				g_poly[j] = g_tmp_2[j];
			}
			else if(0xFF == g_tmp_2[j])
			{
				g_poly[j] = g_tmp_1[j];
			}
			else
			{
				g_poly[j] = gf_add(g_tmp_1[j], g_tmp_2[j]);//add 2 parts
			}
			DEBUG_NOTICE("g_tmp: %d | %x\n", j, g_poly[j]);
		}
	}

	for(i = 0; i < (CODEWORD_LEN + 1); i++)
	{
		DEBUG_NOTICE("g_poly: %d | %x\n", i, g_poly[i]);
	}
	memcpy(g_cmm_poly, g_poly, sizeof(unsigned char) * (CODEWORD_LEN + 1));
	
	return 0;
}

int r_poly_gen(unsigned char *r_v, unsigned char t_p[][CODEWORD_LEN + 1], unsigned char *r_p, long long cal_len)
{
	long long i = 0, j = 0;
	memset(r_p, 0xFF, sizeof(unsigned char) * (CODEWORD_LEN + 1));
	long long locator = 0;
	unsigned char tmp_val = 0xFF;

	for(i = (CODEWORD_LEN - cal_len); i < CODEWORD_LEN; i++)/*!!!locator may be chaged!!!*/
	{
		locator = chnl_rel_order_idx[CODEWORD_LEN - 1 - i];
	
		for(j = 0; j < (CODEWORD_LEN + 1); j++)
		{
			DEBUG_NOTICE("r_poly_cal: %d %d | %x + %x * %x\n", locator, j, r_p[j], r_v[locator], t_p[locator][j]);
#if 0			
			r_p[j] = gf_add(r_p[j],
							gf_multp(r_v[locator], t_p[locator][j]));
#endif			
			if((0xFF == r_v[locator])
				|| (0xFF == t_p[locator][j]))
			{
				tmp_val = 0xFF;
			}
			else if(0x0 == r_v[locator])
			{
				tmp_val = t_p[locator][j];
			}
			else if(0x0 == t_p[locator][j])
			{
				tmp_val = r_v[locator];
			}
			else
			{
				tmp_val = gf_multp(r_v[locator], t_p[locator][j]);
			}
			
			if(0xFF == r_p[j])
			{
				r_p[j] = tmp_val;
			}
			else if(0xFF == tmp_val)
			{
				r_p[j] = r_p[j];
			}
			else
			{
				r_p[j] = gf_add(r_p[j], tmp_val);
			}
			DEBUG_NOTICE("r_poly: %d %d | %x\n", locator, j, r_p[j]);
		}
	}

	return 0;
}

int a_matrix_gen()
{
	long long i = 0, j = 0, k = 0;

	for(i = 0; i < B_MATRIX_SIZE; i++)
	{
		for(j = 0; j < B_MATRIX_SIZE; j++)
		{
			b_matrix[i][j][0] = 0xFF;//x^(-1)
			for(k = 0; k < (CODEWORD_LEN + 1); k++)
			{
				if((0 == i)
					&& (0 == j))
				{
					b_matrix[i][j][k + 1] = g_poly[k];
				}
				else if((1 == i)
						&& (0 == j))
				{
					b_matrix[i][j][k + 1] = r_poly[k];
				}
#if (0 == RE_ENCODING)				
				else if((1 == i)
						&& (1 == j)
						&& ((MESSAGE_LEN - 1) == k))
				{
					b_matrix[i][j][k + 1] = 0;
				}
#else
				else if((1 == i)
						&& (1 == j))
				{
					memset(b_matrix[i][j], 0xFF, sizeof(unsigned char) * (CODEWORD_LEN + 2));
					b_matrix[i][j][0] = 0;//x^(-1)
				}
#endif
				else
				{
					b_matrix[i][j][k + 1] = 0xFF;
				}
			}
		}
	}

	DEBUG_NOTICE("B:\n");
	for(i = 0; i < B_MATRIX_SIZE; i++)
	{
		for(j = 0; j < B_MATRIX_SIZE; j++)
		{
			for(k = 0; k < (CODEWORD_LEN + 2); k++)
			{
				DEBUG_NOTICE("%x ", b_matrix[i][j][k]);
			}
			DEBUG_NOTICE(" | ");
		}
		DEBUG_NOTICE("\n");
	}
	DEBUG_NOTICE("\n");

	return 0;
}

int lp_init()
{
	long long i = 0, j = 0, k = 0;
	long long ld_row = 0, ld_tmp = 0;
	
	memset(lp, 0, sizeof(long long) * B_MATRIX_SIZE);
	memset(ld, 0, sizeof(long long) * B_MATRIX_SIZE);
	
	for(i = 0; i < B_MATRIX_SIZE; i++)//rol
	{
		ld_row = 0;
		for(j = 0; j < B_MATRIX_SIZE; j++)//col
		{
			ld_tmp = 0;
			for(k = 0; k < (CODEWORD_LEN + 2); k++)
			{
				if(0xFF != b_matrix[i][j][k])
				{
					ld_tmp = k;
				}
			}
			if(ld_row <= ld_tmp)
			{
				ld_row = ld_tmp;
				lp[i] = j;
			}
		}
		ld[i] = ld_row;
	}
	
	return 0;
}

int is_weak_popov_form(long long row_size, long long col_size)
{
	long long i = 0;
	long long check_repeat_seq[B_MATRIX_SIZE];
	memset(check_repeat_seq, 0, sizeof(long long) * B_MATRIX_SIZE);
	int is_weak_popov_form_flag = 1;

	lp_init();
	
	for(i = 0; i < B_MATRIX_SIZE; i++)
	{
		DEBUG_NOTICE("lp: %d | %d %d\n", i, lp[i], ld[i]);
		check_repeat_seq[lp[i]]++;
	}
	for(i = 0; i < B_MATRIX_SIZE; i++)
	{
		DEBUG_NOTICE("check_repeat_seq: %d | %d\n", i, check_repeat_seq[i]);
		if(0 == check_repeat_seq[i])
		{
			is_weak_popov_form_flag = 0;
			break;
		}
	}
	DEBUG_NOTICE("is_weak_popov_form_flag: %d\n", is_weak_popov_form_flag);

	return is_weak_popov_form_flag;
}

int ms_trans(long long row_size, long long col_size)
{
	long long i = 0, j = 0, k = 0, l = 0;
	long long t1 = 0, t2 = 0;//t2 > t1
	unsigned char lt_div_coff = 0xFF;
	long long lt_div_ind = 0;
	
	unsigned char tmp_row[B_MATRIX_SIZE][CODEWORD_LEN + 2];
	for(i = 0; i < B_MATRIX_SIZE; i++)
	{
		memset(tmp_row[i], 0xFF, sizeof(unsigned char) * (CODEWORD_LEN + 2));
	}
	
	for(i = 0; i < row_size; i++)
	{
		for(j = 0; j < row_size; j++)
		{
			if(i == j)
			{
				continue;
			}
			
			if(lp[i] == lp[j])
			{
#if 0			
				if(ld[i] < ld[j])
				{
					t1 = i;
					t2 = j;
				}
				else if(ld[i] == ld[j])
				{
					/*t1 < t2*/
					if(b_matrix[i][lp[i]][ld[i]] < b_matrix[j][lp[j]][ld[j]])
					{
						t1 = i;
						t2 = j;
					}
					else
					{
						t1 = j;
						t2 = i;
					}
				}
				else
				{
					t1 = j;
					t2 = i;
				}
#else
				if(ld[i] < ld[j])
				{
					t1 = i;
					t2 = j;
				}
				else
				{
					t1 = j;
					t2 = i;
				}
#endif
				
				DEBUG_NOTICE("t: %d %d\n", t1, t2);
				break;
			}
		}
		
		if(row_size != j)
		{
			lt_div_ind = ld[t2] - ld[t1];
			lt_div_coff = gf_div(b_matrix[t2][lp[t2]][ld[t2]],
								 b_matrix[t1][lp[t1]][ld[t1]]);
			DEBUG_NOTICE("lt_div: %d %x\n", lt_div_ind, lt_div_coff);
								 
			for(j = 0; j < B_MATRIX_SIZE; j++)
			{
				for(k = 0; k < (CODEWORD_LEN + 2 - lt_div_ind); k++)
				{
					tmp_row[j][k + lt_div_ind] = gf_multp(b_matrix[t1][j][k],
														  lt_div_coff);
					DEBUG_NOTICE("tmp_row: %d %d | %x\n", j, k + lt_div_ind, tmp_row[j][k + lt_div_ind]);
				}
			}
			
			for(j = 0; j < B_MATRIX_SIZE; j++)
			{
				for(k = 0; k < (CODEWORD_LEN + 2); k++)
				{
					b_matrix[t2][j][k] = gf_add(b_matrix[t2][j][k],
					                            tmp_row[j][k]);
				}
			}
		}
		
		DEBUG_NOTICE("B:\n");
		for(l = 0; l < B_MATRIX_SIZE; l++)
		{
			for(j = 0; j < B_MATRIX_SIZE; j++)
			{
				for(k = 0; k < (CODEWORD_LEN + 2); k++)
				{
					DEBUG_NOTICE("%x ", b_matrix[l][j][k]);
				}
				DEBUG_NOTICE(" | ");
			}
			DEBUG_NOTICE("\n");
		}
		DEBUG_NOTICE("\n");
	}
	
	return 0;
}

int b_matrix_gen_rev()
{
	long long i = 0, j = 0, k = 0;

	for(i = 0; i < B_MATRIX_SIZE; i++)
	{
		for(j = 0; j < B_MATRIX_SIZE; j++)
		{
			for(k = (CODEWORD_LEN + 1); k >= 0; k--)
			{
				if(((0 == i)
						&& (1 == j))
					||
					((1 == i)
						&& (1 == j)))
				{
#if (0 == RE_ENCODING)				
					if(0xFF != b_matrix[i][j][k])
					{
						a_matrix[i][j][k - (MESSAGE_LEN - 1)] = b_matrix[i][j][k];
					}
					a_matrix[i][j][k] = 0xFF;
#else
					if(0xFF != b_matrix[i][j][k])
					{
						a_matrix[i][j][k - (0 - 1)] = b_matrix[i][j][k];
					}
					a_matrix[i][j][k] = 0xFF;
#endif
				}
				else
				{
					a_matrix[i][j][k] = b_matrix[i][j][k];
				}
			}
		}
	}
	
	DEBUG_NOTICE("A:\n");
	for(i = 0; i < B_MATRIX_SIZE; i++)
	{
		for(j = 0; j < B_MATRIX_SIZE; j++)
		{
			for(k = 0; k < (CODEWORD_LEN + 2); k++)
			{
				DEBUG_NOTICE("%x ", a_matrix[i][j][k]);
				if(0xFF != a_matrix[i][j][k])
				{
					if((k - 1) > max_dx)
					{
						max_dx = (k - 1);
						DEBUG_INFO("max_dx: %ld\n", max_dx);
					}
					if(j > max_dy)
					{
						max_dy = j;
						DEBUG_INFO("max_dy: %ld\n", max_dy);
					}
				}
			}
			DEBUG_NOTICE(" | ");
		}
		DEBUG_NOTICE("\n");
	}
	DEBUG_NOTICE("\n");

	return 0;
}

int tst_vct_trans_init()
{
	long long i = 0, j = 0;
	//DEBUG_IMPOTANT("%s\n", __func__);

  	tst_vct_cmm_trans = (unsigned char*)malloc(sizeof(unsigned char) * CODEWORD_LEN);
  	for(j = 0; j < CODEWORD_LEN; j++)
  	{
		if(0xFF != tst_vct_cmm[j])
		{
			tst_vct_cmm_trans[j] = beta_matrix[tst_vct_cmm[j] + 1][j];
		}
		else
		{
			tst_vct_cmm_trans[j] = beta_matrix[0][j];
		}
		DEBUG_NOTICE("tst_vct_cmm_trans: %ld | %x %x\n", j, intrplt_seq[j], tst_vct_cmm_trans[j]);
  	}

  	tst_vct_trans = (unsigned char**)malloc(sizeof(unsigned char*) * pow_val);
	for(i = 0; i < pow_val; i++)
	{
		tst_vct_trans[i] = (unsigned char*)malloc(sizeof(unsigned char) * CODEWORD_LEN);
  	}
  	for(i = 0; i < pow_val; i++)
	{		
		for(j = 0; j < CODEWORD_LEN; j++)
		{
			
			if(0xFF != tst_vct[i][j])
			{
				tst_vct_trans[i][j] = beta_matrix[tst_vct[i][j] + 1][j];
			}
			else
			{
				tst_vct_trans[i][j] = beta_matrix[0][j];
			}
			DEBUG_NOTICE("tst_vct_trans: %ld %ld | %x %x\n", i, j, intrplt_seq[j], tst_vct_trans[i][j]);
		}
  	}
  	
  	gamma_poly = (unsigned char**)malloc(sizeof(unsigned char*) * pow_val);
	for(i = 0; i < pow_val; i++)
	{
		gamma_poly[i] = (unsigned char*)malloc(sizeof(unsigned char) * (CODEWORD_LEN + 1));
  	}
  	
  	for(i = 0; i < pow_val; i++)
  	{
  		memset(uncommon_decoded_codeword[i], 0xFF, sizeof(unsigned char) * CODEWORD_LEN);
  	}
#if 0	
	for(j = 0; j < CODEWORD_LEN; j++)
  	{
		tst_vct_cmm_trans[j] = tst_vct_trans[1][j];
		DEBUG_NOTICE("tst_vct_cmm_trans_test: %ld | %x %x\n", j, intrplt_seq[j], tst_vct_cmm_trans[j]);
  	}
#endif	
	return 0;
}

int tst_vct_trans_exit()
{
	long long i = 0;

	free(tst_vct_cmm_trans);
	tst_vct_cmm_trans = NULL;
	
	for(i = 0; i < pow_val; i++)
	{
		free(tst_vct_trans[i]);
		tst_vct_trans[i] = NULL;
	}
	free(tst_vct_trans);
	tst_vct_trans = NULL;
	
	for(i = 0; i < pow_val; i++)
	{
		free(gamma_poly[i]);
		gamma_poly[i] = NULL;
	}
	free(gamma_poly);
	gamma_poly = NULL;
	
	return 0;
}

int t_wave_poly_construct(unsigned char locator_j, unsigned char *L)
{
	DEBUG_NOTICE("%s: %x\n", __func__, locator_j);
	long long i = 0, j = 0;
	unsigned char v_tmp_1[CODEWORD_LEN + 1], v_tmp_2[CODEWORD_LEN + 1];
	unsigned char tmp_div = 0, tmp_inv = 0xFF;
	unsigned char rel_flag = 0;

	memset(L, 0xFF, sizeof(unsigned char) * (CODEWORD_LEN + 1));
	L[0] = 0;

	for(i = 1; i < GF_FIELD; i++)
	{
		if(power_polynomial_table[i][0] == locator_j)
		{
			continue;
		}
		rel_flag = 0;
		for(j = 0; j < MESSAGE_LEN; j++)
		{
			if(power_polynomial_table[i][0] == rel_group_seq[j])
			{
				rel_flag = 1;
				break;
			}
		}
		if(1 == rel_flag)
		{
			continue;
		}
		
		memset(v_tmp_1, 0xFF, sizeof(unsigned char) * (CODEWORD_LEN + 1));
		memset(v_tmp_2, 0xFF, sizeof(unsigned char) * (CODEWORD_LEN + 1));

		for(j = 0; j < CODEWORD_LEN; j++)
		{
			v_tmp_1[j + 1] = L[j];//increase degree because of x term
			//DEBUG_NOTICE("v_tmp_1: %d | %x\n", j + 1, v_tmp_1[j + 1]);

			if(0x0 == L[j])
			{
				v_tmp_2[j] = power_polynomial_table[i][0];
				//DEBUG_NOTICE("v_tmp_2: %d | %x=%x*%x\n", j, v_tmp_2[j], L[j], power_polynomial_table[i][0]);
				continue;
			}
			if(0xFF != L[j])
			{
				v_tmp_2[j] = gf_multp(L[j], power_polynomial_table[i][0]);//calculation of a_i term
			}
			//DEBUG_NOTICE("v_tmp_2: %d | %x=%x*%x\n", j, v_tmp_2[j], L[j], power_polynomial_table[i][0]);
		}

		for(j = 0; j < (CODEWORD_LEN + 1); j++)
		{
			if(0xFF == v_tmp_1[j])
			{
				L[j]= v_tmp_2[j];
				//DEBUG_NOTICE("v_tmp: %d %d | %x\n", i, j, L[j]);
				continue;
			}
			if(0xFF == v_tmp_2[j])
			{
				L[j]= v_tmp_1[j];
				//DEBUG_NOTICE("v_tmp: %d %d | %x\n", i, j, L[j]);
				continue;
			}
			L[j] = gf_add(v_tmp_1[j], v_tmp_2[j]);//add 2 parts
			//DEBUG_NOTICE("v_tmp: %d %d | %x\n", i, j, L[j]);
		}
	}

	tmp_div = t_div[locator_j];

	for(i = 0; i < (CODEWORD_LEN + 1); i++)
	{
		if(0x0 == L[i])
		{
			L[i] = tmp_div;
			DEBUG_NOTICE("t_wave_poly: %d %d | %x\n", locator_j, i, L[i]);
			continue;
		}
		if(0x0 == tmp_div)
		{
			DEBUG_NOTICE("t_wave_poly: %d %d | %x\n", locator_j, i, L[i]);
			continue;
		}
	
		L[i] = gf_multp(L[i], tmp_div);
		DEBUG_NOTICE("t_wave_poly: %d %d | %x\n", locator_j, i, L[i]);
	}
	
	return 0;
}

int lagrange_wave_poly_construct()
{
	DEBUG_NOTICE("%s\n", __func__);
	long long i = 0, j = 0;
	unsigned char rel_flag = 0;

	for(i = 1; i < GF_FIELD; i++)
	{
		rel_flag = 0;
		for(j = 0; j < MESSAGE_LEN; j++)
		{
			if((i - 1) == rel_group_seq[j])
			{
				rel_flag = 1;
				break;
			}
		}
		if(1 == rel_flag)
		{
			memset(t_wave_poly[i - 1], 0xFF, sizeof(unsigned char) * (CODEWORD_LEN + 1));
			continue;
		}
		t_wave_poly_construct(power_polynomial_table[i][0], t_wave_poly[i - 1]);
	}

	return 0;
}

int g_r_poly_div_v()
{
	long long i = 0, j = 0;
	unsigned char quotien[CODEWORD_LEN + 1];
	unsigned char remainder[CODEWORD_LEN + 1];
	unsigned char v_t_tmp[MESSAGE_LEN + 1];
	unsigned char v_t_div[2];
	unsigned char tmp_flag = 0;
#if 0
	memset(quotien, 0xFF, sizeof(unsigned char) * (CODEWORD_LEN + 1));
	memset(remainder, 0xFF, sizeof(unsigned char) * (CODEWORD_LEN + 1));
	gf_div_q_r(g_poly, CODEWORD_LEN + 1,
			   v, MESSAGE_LEN + 1,
			   quotien, CODEWORD_LEN + 1,
			   remainder, CODEWORD_LEN + 1);
	memcpy(g_poly, quotien, sizeof(unsigned char) * (CODEWORD_LEN + 1));
	for(i = 0; i < (CODEWORD_LEN + 1); i++)
	{
		DEBUG_INFO("g_poly: %ld | %x\n", i, g_poly[i]);
	}
#else	
	g_wave_poly_gen();
#endif	
#if 0	
	memset(quotien, 0xFF, sizeof(unsigned char) * (CODEWORD_LEN + 1));
	memset(remainder, 0xFF, sizeof(unsigned char) * (CODEWORD_LEN + 1));
	gf_div_q_r(r_poly, CODEWORD_LEN + 1,
			   v, MESSAGE_LEN + 1,
			   quotien, CODEWORD_LEN + 1,
			   remainder, CODEWORD_LEN + 1);
	memcpy(r_poly, quotien, sizeof(unsigned char) * (CODEWORD_LEN + 1));
#endif	
	memset(quotien, 0xFF, sizeof(unsigned char) * (CODEWORD_LEN + 1));
	for(i = 0; i < CODEWORD_LEN; i++)
	{
		tmp_flag = 0;
		for(j = 0; j < MESSAGE_LEN; j++)
		{
			if(i == rel_group_seq[j])
			{
				tmp_flag = 1;
			}
		}
		if(1 == tmp_flag)
		{
			continue;
		}
		for(j = 0; j < YITA; j++)
		{
			if(i == chnl_rel_order_idx[j])
			{
				tmp_flag = 1;
			}
		}
		if(1 == tmp_flag)
		{
			continue;
		}
		
		for(j = 0; j < (CODEWORD_LEN + 1); j++)
		{
			DEBUG_INFO("r_poly_quotien: %ld %ld | %x | %x %x\n", i, j, quotien[j], tst_vct_cmm_trans[i], t_wave_poly[i][j]);
			quotien[j] = gf_add(quotien[j], gf_multp(tst_vct_cmm_trans[i], t_wave_poly[i][j]));
		}
	}
	memcpy(r_poly, quotien, sizeof(unsigned char) * (CODEWORD_LEN + 1));
	for(i = 0; i < (CODEWORD_LEN + 1); i++)
	{
		DEBUG_INFO("r_poly: %ld | %x\n", i, r_poly[i]);
	}
	
	return 0;
}

int cmm_matrix_init()
{
	long long i = 0, j = 0, k = 0;
	
	for(i = 0; i < B_MATRIX_SIZE; i++)
	{
		for(j = 0; j < B_MATRIX_SIZE; j++)
		{
			for(k = 0; k < (CODEWORD_LEN + 2); k++)
			{
				a_cmm_matrix[i][j][k] = a_matrix[i][j][k];
			}
		}
	}
	
	return 0;
}

int gamma_poly_gen(long long tv_idx)
{
	long long i = 0;

	r_poly_gen(tst_vct_trans[tv_idx], t_wave_poly, gamma_poly[tv_idx], YITA);

	for(i = 0; i < (CODEWORD_LEN + 1); i++)
	{
		if(0xFF != gamma_poly[tv_idx][i])
		{
			DEBUG_INFO("gamma_poly: %ld %ld | %x\n", tv_idx, i, gamma_poly[tv_idx][i]);
		}
	}

	return 0;
}

int a_matrix_tv_gen(long long tv_idx)
{
	DEBUG_IMPOTANT("%s: %ld\n", __func__, __LINE__);
	long long i = -1, j = -1, k = -1;
	
	unsigned char poly_prod[CODEWORD_LEN + 1];
	unsigned char poly_cmm_coef[CODEWORD_LEN + 1];
	long long degree_poly_cmm_coef = 0, degree_gamma_poly = 0, degree_poly_prod = 0;
	
	for(i = 0; i < B_MATRIX_SIZE; i++)
	{
		for(j = 0; j < B_MATRIX_SIZE; j++)
		{
			for(k = 0; k < (CODEWORD_LEN + 2); k++)
			{
				a_matrix[i][j][k] = a_cmm_matrix[i][j][k];
			}
		}
	}
	DEBUG_IMPOTANT("%s: %ld\n", __func__, __LINE__);
	for(i = 0; i < B_MATRIX_SIZE; i++)
	{
		memset(poly_prod, 0xFF, sizeof(unsigned char) * (CODEWORD_LEN + 1));
		memcpy(poly_cmm_coef, a_cmm_matrix[i][1] + 1, sizeof(unsigned char) * (CODEWORD_LEN + 1));
		
		for(j = 0; j < (CODEWORD_LEN + 1); j++)
		{
			if(0xFF != poly_cmm_coef[j])
			{
				degree_poly_cmm_coef = j;
			}
			if(0xFF != gamma_poly[tv_idx][j])
			{
				degree_gamma_poly = j;
			}
		}
		degree_poly_prod = degree_poly_cmm_coef + degree_gamma_poly;
		DEBUG_INFO("degree_poly: %ld %ld %ld\n", degree_poly_cmm_coef, degree_gamma_poly, degree_poly_prod);
		
		DEBUG_IMPOTANT("%s: %ld\n", __func__, __LINE__);
#if 0
		gf_multp_poly(poly_cmm_coef, CODEWORD_LEN + 1,
		              gamma_poly[tv_idx], CODEWORD_LEN + 1,
		              poly_prod, CODEWORD_LEN + 1);
#else
		gf_multp_poly(poly_cmm_coef, degree_poly_cmm_coef + 1,
		              gamma_poly[tv_idx], degree_gamma_poly + 1,
		              poly_prod, degree_poly_prod + 1);
#endif
		DEBUG_IMPOTANT("%s: %ld\n", __func__, __LINE__);
		DEBUG_NOTICE("poly_prod: ");
		for(j = 0; j < (CODEWORD_LEN + 1); j++)
		{
			DEBUG_NOTICE("%x ", poly_prod[j]);
		}
		DEBUG_NOTICE("\n");
		
		for(j = 1; j < (CODEWORD_LEN + 2); j++)
		{
			a_matrix[i][0][j] = gf_add(a_cmm_matrix[i][0][j], poly_prod[j - 1]);
		}
	}
	
	DEBUG_NOTICE("tv_idx: %d\n", tv_idx);
	DEBUG_NOTICE("A:\n");
	for(i = 0; i < B_MATRIX_SIZE; i++)
	{
		for(j = 0; j < B_MATRIX_SIZE; j++)
		{
			for(k = 0; k < (CODEWORD_LEN + 2); k++)
			{
				DEBUG_NOTICE("%x ", a_matrix[i][j][k]);
			}
			DEBUG_NOTICE(" | ");
		}
		DEBUG_NOTICE("\n");
	}
	DEBUG_NOTICE("\n");

	for(i = 0; i < B_MATRIX_SIZE; i++)
	{
		for(j = 0; j < B_MATRIX_SIZE; j++)
		{
			b_matrix[i][j][0] = 0xFF;//x^(-1)
			for(k = 0; k < (CODEWORD_LEN + 1); k++)
			{
				if(0 == j)
				{
					b_matrix[i][j][k] = a_matrix[i][j][k];
				}
#if (0 == RE_ENCODING)
				else if(1 == j)
				{
					if(MESSAGE_LEN > k)
					{
						b_matrix[i][j][k] = 0xFF;
						continue;
					}
					b_matrix[i][j][k] = a_matrix[i][j][k - MESSAGE_LEN];
				}
#else
				else if(1 == j)
				{
					if(CODEWORD_LEN == k)
					{
						b_matrix[i][j][k] = 0xFF;
						continue;
					}
					b_matrix[i][j][k] = a_matrix[i][j][k + 1];//* x^(-1)
				}
#endif
				else
				{
					b_matrix[i][j][k] = 0xFF;
				}
			}
		}
	}

	DEBUG_NOTICE("B:\n");
	for(i = 0; i < B_MATRIX_SIZE; i++)
	{
		for(j = 0; j < B_MATRIX_SIZE; j++)
		{
			for(k = 0; k < (CODEWORD_LEN + 2); k++)
			{
				DEBUG_NOTICE("%x ", b_matrix[i][j][k]);
			}
			DEBUG_NOTICE(" | ");
		}
		DEBUG_NOTICE("\n");
	}
	DEBUG_NOTICE("\n");
	
	return 0;
}

int br_poly_trans(long long tv_idx)
{
	long long i = 0, j = 0, k = 0, l = 0;
	long long row_choose = 0;
	long long row_deg[B_MATRIX_SIZE];
	long long row_deg_tmp = 0;
	//DEBUG_NOTICE("AAAB: %x\n", uncommon_decoded_codeword[0][0]);
	memset(uncommon_term_c_choose[tv_idx], 0xFF, sizeof(unsigned char) * term_size_p);
	//DEBUG_NOTICE("AAA: %x\n", uncommon_decoded_codeword[0][0]);
	memset(row_deg, 0, sizeof(long long) * B_MATRIX_SIZE);
	
	for(i = 0; i < B_MATRIX_SIZE; i++)
	{
		for(j = 0; j < B_MATRIX_SIZE; j++)
		{
			for(k = (CODEWORD_LEN + 1); k >= 0; k--)
			{
				if(0xFF != a_matrix[i][j][k])
				{
					break;
				}
			}
			row_deg_tmp = (k - 1) + Y_WEIGHT * j;
			if(row_deg[i] < row_deg_tmp)
			{
				row_deg[i] = row_deg_tmp;
			}
		}
		DEBUG_NOTICE("row_deg: %ld | %ld\n", i, row_deg[i]);
	}
	
	row_deg_tmp = row_deg[0];
	for(i = 0; i < B_MATRIX_SIZE; i++)
	{
		if(row_deg_tmp > row_deg[i])
		{
			row_deg_tmp = row_deg[i];
			row_choose = i;
		}
	}
	DEBUG_NOTICE("row_choose: %ld | %ld %ld | %ld\n", tv_idx, row_deg_tmp, row_choose, term_size_p);
	
	for(j = 0; j < B_MATRIX_SIZE; j++)
	{
		for(k = 0; k < (CODEWORD_LEN + 2); k++)
		{
			if(0xFF != a_matrix[row_choose][j][k])
			{
				for(l = 0; l < term_size_p; l++)
				{
					if(((k - 1) == g_term_x[l])
						&& (j == g_term_y[l]))
					{
						DEBUG_INFO("uncommon_term_c_set: %ld | %ld %ld | %x\n",
								   l,
								   g_term_x[l],
								   g_term_y[l],
								   a_matrix[row_choose][j][k]);
						break;
					}
				}
				uncommon_term_c_choose[tv_idx][l] = a_matrix[row_choose][j][k];
			}
		}
	}
	
	for(l = 0; l < term_size_p; l++)
	{
		if(0xFF != uncommon_term_c_choose[tv_idx][l])
		{
			DEBUG_INFO("uncommon_term_c_choose: %ld | %ld %ld | %x\n",
					   tv_idx,
					   g_term_x[l],
					   g_term_y[l],
					   uncommon_term_c_choose[tv_idx][l]);
		}
	}
	
	return 0;
}

int br_cmm_interpolation()
{
	memcpy(g_poly, g_cmm_poly, sizeof(unsigned char) * (CODEWORD_LEN + 1));

	r_poly_gen(tst_vct_cmm_trans, t_poly, r_poly, CODEWORD_LEN);

	lagrange_wave_poly_construct();
	//gf_count_switch(1);
	g_r_poly_div_v();//simple implementation may be used instead of this
	//gf_count_switch(0);
	a_matrix_gen();
#if 0
	while(0 == is_weak_popov_form(B_MATRIX_SIZE, B_MATRIX_SIZE))
	{
		ms_trans(B_MATRIX_SIZE, B_MATRIX_SIZE);
	}
#endif	
	b_matrix_gen_rev();

	cmm_matrix_init();

	return 0;
}

int br_uncmm_interpolation(long long tv_idx)
{
	DEBUG_IMPOTANT("%s: %ld\n", __func__, tv_idx);
	long long time_cnt = 0;

	gamma_poly_gen(tv_idx);
	a_matrix_tv_gen(tv_idx);
	while(0 == is_weak_popov_form(B_MATRIX_SIZE, B_MATRIX_SIZE))
	{
		ms_trans(B_MATRIX_SIZE, B_MATRIX_SIZE);
		time_cnt++;
		
		if(10000 < time_cnt)
		{
			DEBUG_SYS("MS timeout: %ld\n", time_cnt);
			break;
		}
	}
	b_matrix_gen_rev();
	
	br_poly_trans(tv_idx);

	uncommon_fast_msg_get(tv_idx);
}

int br_cal_offline()
{
#if 0
	g_poly_gen();
#endif	
	lagrange_poly_construct();
	
	return 0;
}

int br_test()
{
	long long i = 0;

	DEBUG_IMPOTANT("%s\n", __func__);
	g_poly_gen();
	lagrange_poly_construct();

	tst_vct_trans_init();

	r_poly_gen(tst_vct_cmm_trans, t_poly, r_poly, CODEWORD_LEN);

	g_r_poly_div_v();//simple implementation may be used instead of this

	lagrange_wave_poly_construct();

	a_matrix_gen();
	while(0 == is_weak_popov_form(B_MATRIX_SIZE, B_MATRIX_SIZE))
	{
		ms_trans(B_MATRIX_SIZE, B_MATRIX_SIZE);
	}
	b_matrix_gen_rev();

	cmm_matrix_init();

	for(i = 0; i < pow_val; i++)
	{
		gamma_poly_gen(i);
		a_matrix_tv_gen(i);
		while(0 == is_weak_popov_form(B_MATRIX_SIZE, B_MATRIX_SIZE))
		{
			ms_trans(B_MATRIX_SIZE, B_MATRIX_SIZE);
		}
		b_matrix_gen_rev();
		
		br_poly_trans(i);
		
		uncommon_fast_msg_get(i);
	}

	tst_vct_trans_exit();

	return 0;
}
