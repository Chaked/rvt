/* Headers for predefined outlined functions */
float rv_mult(float x, float y);
float rv_div(float x, float y);
int rv_mod (int x, int y);
# 1 "/home/rvt/rvtweb/d17d2bc0-3d66-11e8-be9f-2198b2796b54/p1.c"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 1 "<command-line>" 2
# 1 "/home/rvt/rvtweb/d17d2bc0-3d66-11e8-be9f-2198b2796b54/p1.c"
int fact(int n){
   if (n <= 1) return 1;
   return n * fact(n-1);
}

int main(){
    int n;
    return fact(n);
}
