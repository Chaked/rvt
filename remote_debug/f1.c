int id(int n) {
    if (n <= -1) return 0;
    if (n == 0) return id(n - 1);
    return 1 + id(n - 1);
}

int fact(int n) {
    if (n <= 1) return 1;
    return id(n) * fact(n-1);
}

int main() {
    int n;
    return fact(n);
}