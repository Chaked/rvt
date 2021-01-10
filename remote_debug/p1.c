int id(int n) {
	if (n <= 0) return 0;
	return 1 + id(n - 1);
}

int check(int a, int b) {
	return id(a) == a && id(b) == b;
}

int mult(int a, int b) {
	int d = 0;
	int c = 1;
	for (int i = 1; i <= b; ++i)
		if (check(a, b))
			d += a;
		else
			c++;
	return d;
}

int main(int x, char* argv[]) {
	if (x >= 18 && x < 22)
		return mult(x, 20);
	return 0;
}
