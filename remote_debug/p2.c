int id(int n) {
	if (n <= 0) return 0;
	if (n == 1) return 1;
	return 1 + id(n - 1);
}

int check(int a, int b) {
	return id(a) == a && id(b) == b;
}

int mult(int a, int b) {
	int c = 0;
	int d = 1;
	for (int i = 1; i <= a; ++i)
		if (check(a, b))
			c += b;
		else
			d++;
	return c;
}

int main(int x, char* argv[]) {
	if (x >= 18 && x < 22)
		return mult(x, 20);
	return 0;
}
