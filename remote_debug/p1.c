/* type-specific outlined function created by prependOutlineFunction() */
int rv_mult_int__int_(int x, int y);


float  rv_mult(float  x, float  y);
float  rv_div(float  x, float  y);
int  rv_mod(int  x, int  y);
void  __CPROVER_assume(_Bool  rv_arg_0);
int  a[25];
void  bubble_sort(int* a, int  sz);

int  foo_function(int* a, int  n);

int  main();

unsigned char  Loop_bubble_sort_for1(int* a, int* rvp_i);

unsigned char  Loop_bubble_sort_for1_for1(int* a, int  i, int* rvp_j);


void  bubble_sort(int* a, int  sz)
{
    {
        int  i = sz - 1;

        {
            Loop_bubble_sort_for1(a, &i);
        }

    }

}

unsigned char  Loop_bubble_sort_for1(int* a, int* rvp_i)
{
    if (!(*rvp_i > 0))
        return 0;

    {
        {
            int  j = 0;

            {
                unsigned char  rv_ltc_val;

                rv_ltc_val = Loop_bubble_sort_for1_for1(a, *rvp_i, &j);
            }

        }

        *rvp_i = *rvp_i - 1;
    }

    {
        return Loop_bubble_sort_for1(a, rvp_i);
    }
    return 0;
}

unsigned char  Loop_bubble_sort_for1_for1(int* a, int  i, int* rvp_j)
{
    if (!(*rvp_j < i))
        return 0;

    {
        if (*(a + *rvp_j) < *(a + *rvp_j + 1))
        {
            int  t = *(a + *rvp_j);

            *(a + *rvp_j) = *(a + *rvp_j + 1);
            *(a + *rvp_j + 1) = t;
        }

        *rvp_j = *rvp_j + 1;
    }

    {
        return Loop_bubble_sort_for1_for1(a, i, rvp_j);
    }
    return 0;
}



unsigned char  Loop_foo_function_while1(int* a, int* rvp_i, int* rvp_j, int* rvp_rvretval);


int  foo_function(int* a, int  n)
{
    int  rvretval = 0;
    int  i = n;
    int  j = 0;

    {
        Loop_foo_function_while1(a, &i, &j, &rvretval);
    }

    return j;
}

unsigned char  Loop_foo_function_while1(int* a, int* rvp_i, int* rvp_j, int* rvp_rvretval)
{
    if (!(*rvp_i >= 0))
        return 0;

    {
        bubble_sort(a + rv_mult_int__int_(5, *rvp_j), 5);
        *rvp_i = *rvp_i - 1;
        (*rvp_j)++;
    }

    {
        return Loop_foo_function_while1(a, rvp_i, rvp_j, rvp_rvretval);
    }
    return 0;
}



int  main()
{
    foo_function(a, 25);
    return 0;
}



void __CPROVER_assume(_Bool);

/* Hub functions for indirect function calls: */
