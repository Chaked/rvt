/* Headers for predefined outlined functions */
float rv_mult(float x, float y);
float rv_div(float x, float y);
int rv_mod (int x, int y);
# 1 "/home/rvt/rvtweb/272b5ae0-74dc-11e8-9289-1915984c2ee5/p2.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "/home/rvt/rvtweb/272b5ae0-74dc-11e8-9289-1915984c2ee5/p2.c"
int fact(int n){
   if (n <= 0) return 1;
   return n * fact(n-1);
}

int main(){
    int n;
    return fact(n);
}