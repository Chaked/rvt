#include "rv_declarations.h"

/*** global declarations side 0: ***/
float  rvs0_rv_mult(float  x, float  y);
float  rvs0_rv_div(float  x, float  y);
int  rvs0_rv_mod(int  x, int  y);
int  rvs0_n;
int  chk0_sum(int  n);
int  rvs0_main();
int  rvs0_sum(int  n);
void  __CPROVER_assume(_Bool  rv_arg_2);

/*** global declarations side 1: ***/
float  rvs1_rv_mult(float  x, float  y);
float  rvs1_rv_div(float  x, float  y);
int  rvs1_rv_mod(int  x, int  y);
int  rvs1_n;
int  rvs1_ident(int  n);
int  chk1_sum(int  n);
int  rvs1_main();
int  rvs1_sum(int  n);
void  __CPROVER_assume(_Bool  rv_arg_3);

/*** end of global declarations side 1: ***/
/*** end of global declarations. ***/

/*** Functions side 0: ***/
int  rvs0_sum(int  n);
int  chk0_sum(int  n)
{
  if (n <= 1)
    return n;
  return n + rvs0_sum(n - 1);
}


/*** Functions side 1: ***/
int  rvs1_ident(int  n)
{
  return n;
}

int  rvs1_sum(int  n);
int  chk1_sum(int  n)
{
  n = rvs1_ident(n + 1) - 1;
  if (n <= 1)
    return n;
  return n + rvs1_sum(n - 1);
}


  /* Declarations of the CBMC uninterpreted functions */
int  __CPROVER_uninterpreted_retval(int );

  /* CBMC-UF side 0: */ 
int  rvs0_sum(int  n)
{
  int  retval;

  /* Declarations: */


  /* Each output is assigned a UF:*/
  retval= __CPROVER_uninterpreted_retval(n);

  return retval;
}


  /* CBMC-UF side 1: */ 
int  rvs1_sum(int  n)
{
  int  retval;

  /* Declarations: */


  /* Each output is assigned a UF:*/
  retval= __CPROVER_uninterpreted_retval(n);

  return retval;
}

  /* now starting main */

int main()
{
  _Bool equal = 1;
  /* Declarations: */
  int  retval0;	/* Generated by:  gen_retval_declarations/ rv_temps.cpp:269*/
  int  retval1;	/* Generated by:  gen_retval_declarations/ rv_temps.cpp:269*/
  int  rvs0_n;	/* Generated by:  gen_arg_decl(107)/ gen_decl_low(148)/ rv_temps.cpp:274*/
  int  rvs1_n;	/* Generated by:  gen_arg_decl(107)/ gen_decl_low(148)(107)/ gen_decl_low(148)/ rv_temps.cpp:274*/

  /* output: */
  /* Allocations for side 0: */
  /* Allocations for side 1: */

  /* Assume input args are equal: */ 
  rvs0_n = rvs1_n;	/* Generated by:  gen_args_equality(608)(613)(379)(293)/ rv_temps.cpp:362*/

  /* run each side's main() */
  retval0 = chk0_sum(rvs0_n);
  retval1 = chk1_sum(rvs1_n);
  /* Assertions: */

  /* Compare return values: */ 
  assert( retval0 == retval1 );	/* Generated by:  gen_main(608)(613)(379)(309)/ rv_temps.cpp:352*/

  /* Compare output args: */ 


  return 0;
}