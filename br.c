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

unsigned char g_poly[CODEWORD_LEN + 1];
unsigned char r_poly[CODEWORD_LEN + 1];
unsigned char t_poly[CODEWORD_LEN][CODEWORD_LEN + 1];
unsigned char b_matrix[B_MATRIX_SIZE][B_MATRIX_SIZE][CODEWORD_LEN + 1];
unsigned char a_matrix[B_MATRIX_SIZE][B_MATRIX_SIZE][CODEWORD_LEN + 1];

long long lp[B_MATRIX_SIZE];
long long ld[B_MATRIX_SIZE];

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
			DEBUG_NOTICE("v_tmp_1: %d | %x\n", j + 1, v_tmp_1[j + 1]);

			if(0x0 == L[j])
			{
				v_tmp_2[j] = power_polynomial_table[i][0];
				DEBUG_NOTICE("v_tmp_2: %d | %x=%x*%x\n", j, v_tmp_2[j], L[j], power_polynomial_table[i][0]);
				continue;
			}
			if(0xFF != L[j])
			{
				v_tmp_2[j] = gf_multp(L[j], power_polynomial_table[i][0]);//calculation of a_i term
			}
			DEBUG_NOTICE("v_tmp_2: %d | %x=%x*%x\n", j, v_tmp_2[j], L[j], power_polynomial_table[i][0]);
		}

		for(j = 0; j < (CODEWORD_LEN + 1); j++)
		{
			if(0xFF == v_tmp_1[j])
			{
				L[j]= v_tmp_2[j];
				DEBUG_NOTICE("v_tmp: %d %d | %x\n", i, j, L[j]);
				continue;
			}
			if(0xFF == v_tmp_2[j])
			{
				L[j]= v_tmp_1[j];
				DEBUG_NOTICE("v_tmp: %d %d | %x\n", i, j, L[j]);
				continue;
			}
			L[j] = gf_add(v_tmp_1[j], v_tmp_2[j]);//add 2 parts
			DEBUG_NOTICE("v_tmp: %d %d | %x\n", i, j, L[j]);
		}
	}

	for(i = 1; i < GF_FIELD; i++)
	{
		if(power_polynomial_table[i][0] == locator_j)
		{
			continue;
		}

		tmp_inv = gf_div(0x0, gf_add(locator_j, power_polynomial_table[i][0]));
		DEBUG_NOTICE("tmp_inv: %d | %x\n", i, tmp_inv);
		tmp_div = gf_multp(tmp_div, tmp_inv);
		DEBUG_NOTICE("tmp_div: %d | %x\n", i, tmp_div);
	}

	for(i = 0; i < (CODEWORD_LEN + 1); i++)
	{
		if(0x0 == L[i])
		{
			L[i] = tmp_div;
			DEBUG_NOTICE("L: %d | %x\n", i, L[i]);
			continue;
		}
		if(0x0 == tmp_div)
		{
			DEBUG_NOTICE("L: %d | %x\n", i, L[i]);
			continue;
		}
	
		L[i] = gf_multp(L[i], tmp_div);
		DEBUG_NOTICE("L: %d | %x\n", i, L[i]);
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
			g_poly[j] = gf_add(g_tmp_1[j], g_tmp_2[j]);//add 2 parts
			DEBUG_NOTICE("g_tmp: %d | %x\n", j, g_poly[j]);
		}
	}

	for(i = 0; i < (CODEWORD_LEN + 1); i++)
	{
		DEBUG_NOTICE("g_poly: %d | %x\n", i, g_poly[i]);
	}
	
	return 0;
}

int r_poly_gen()
{
	long long i = 0, j = 0;
	memset(r_poly, 0xFF, sizeof(unsigned char) * (CODEWORD_LEN + 1));

	for(i = 0; i < CODEWORD_LEN; i++)
	{
		for(j = 0; j < (CODEWORD_LEN + 1); j++)
		{
			DEBUG_NOTICE("r_poly_cal: %d %d | %x + %x * %x\n", i, j, r_poly[j], received_polynomial[i], t_poly[i][j]);
			r_poly[j] = gf_add(r_poly[j],
							   gf_multp(received_polynomial[i], t_poly[i][j]));
			DEBUG_NOTICE("r_poly: %d %d | %x\n", i, j, r_poly[j]);
		}
	}

	return 0;
}

int a_matrix_gen()
{
	long long i = 0, j = 0, k = 0;
	DEBUG_NOTICE("B:\n");
	for(i = 0; i < B_MATRIX_SIZE; i++)
	{
		for(j = 0; j < B_MATRIX_SIZE; j++)
		{
			for(k = 0; k < (CODEWORD_LEN + 1); k++)
			{
				if((0 == i)
					&& (0 == j))
				{
					b_matrix[i][j][k] = g_poly[k];
				}
				else if((1 == i)
						&& (0 == j))
				{
					b_matrix[i][j][k] = r_poly[k];
				}
				else if((1 == i)
						&& (1 == j)
						&& ((MESSAGE_LEN - 1) == k))
				{
					b_matrix[i][j][k] = 0;
				}
				else
				{
					b_matrix[i][j][k] = 0xFF;
				}
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
			for(k = 0; k < (CODEWORD_LEN + 1); k++)
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
	
	unsigned char tmp_row[B_MATRIX_SIZE][CODEWORD_LEN + 1];
	for(i = 0; i < B_MATRIX_SIZE; i++)
	{
		memset(tmp_row[i], 0xFF, sizeof(unsigned char) * (CODEWORD_LEN + 1));
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
				if(ld[i] < ld[j])
				{
					t1 = i;
					t2 = j;
				}
				else if(ld[i] == ld[j])
				{
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
				for(k = 0; k < (CODEWORD_LEN + 1 - lt_div_ind); k++)
				{
					tmp_row[j][k + lt_div_ind] = gf_multp(b_matrix[t1][j][k],
														  lt_div_coff);
					DEBUG_NOTICE("tmp_row: %d %d | %x\n", j, k + lt_div_ind, tmp_row[j][k + lt_div_ind]);
				}
			}
			
			for(j = 0; j < B_MATRIX_SIZE; j++)
			{
				for(k = 0; k < (CODEWORD_LEN + 1); k++)
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
				for(k = 0; k < (CODEWORD_LEN + 1); k++)
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
			for(k = 0; k < (CODEWORD_LEN + 1); k++)
			{
				if(((0 == i)
						&& (1 == j))
					||
					((1 == i)
						&& (1 == j)))
				{
					if(0xFF != b_matrix[i][j][k])
					{
						a_matrix[i][j][k - (MESSAGE_LEN - 1)] = b_matrix[i][j][k];
					}
					a_matrix[i][j][k] = 0xFF;
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
			for(k = 0; k < (CODEWORD_LEN + 1); k++)
			{
				DEBUG_NOTICE("%x ", a_matrix[i][j][k]);
			}
			DEBUG_NOTICE(" | ");
		}
		DEBUG_NOTICE("\n");
	}
	DEBUG_NOTICE("\n");

	return 0;
}

int br_test()
{
	int val = 0;

	DEBUG_IMPOTANT("%s\n", __func__);
	g_poly_gen();
	lagrange_poly_construct();
	r_poly_gen();
	a_matrix_gen();
	while(0 == is_weak_popov_form(B_MATRIX_SIZE, B_MATRIX_SIZE))
	{
		ms_trans(B_MATRIX_SIZE, B_MATRIX_SIZE);
	}
	b_matrix_gen_rev();

	return 0;
}