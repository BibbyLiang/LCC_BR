#ifndef BR_H
#define BR_H

#include "cfg_decoding.h"

extern long long g_time_cnt;
extern unsigned char **tst_vct_trans;
#if (1 == CFG_NEW_TST_VCT)
extern unsigned char **new_tst_vct_trans;
#endif

extern int t_poly_construct(unsigned char locator_j, unsigned char *L);
extern int lagrange_poly_construct();
extern int tst_vct_trans_init();
extern int tst_vct_trans_exit();
extern int br_cmm_interpolation();
extern int br_uncmm_interpolation(long long tv_idx);
extern int br_cal_offline();
extern int br_test();

#if (1 == CFG_NEW_TST_VCT)
extern int new_tst_vct_trans_init();
extern int new_tst_vct_trans_exit();
#endif

#endif