
typedef enum {false, true} bool;

extern int __VERIFIER_nondet_int(void);

int main() {
  int n_number, numerator, denominator, nmul, dmul, r_number, nCr;
  n_number = __VERIFIER_nondet_int();
  numerator = __VERIFIER_nondet_int();
  denominator = __VERIFIER_nondet_int();
  nmul = __VERIFIER_nondet_int();
  dmul = __VERIFIER_nondet_int();
  r_number = __VERIFIER_nondet_int();
  nCr = __VERIFIER_nondet_int();

  if (n_number >= 1) {
    numerator = 1;
    denominator = 1;
    nmul = n_number;
    dmul = r_number;
    nCr = 1;
    if (n_number >= r_number) {
      /*
      if (nondet_bool()) { // 2 -> 5 -> 6
	if (! (numerator < 1)) { return; }
	nCr = numerator / denominator;
	return;
      }
      */
      
      while (nCr >= 1) {
	/*
	if (nondet_bool()) { // 2 -> 5 -> 6
	  if (! (numerator < 1)) { return; }
	  nCr = numerator / denominator;
	  return;
	}
	*/
	numerator = numerator * nmul;
	nmul = nmul - 1;
	denominator = denominator * dmul;
	dmul = dmul - 1;
      }
      /*
      if (nondet_bool()) { // 2 -> 5 -> 6
	if (! (numerator < 1)) { return; }
	nCr = numerator / denominator;
	return;
      }
      */
    } else {
    }
  }
  return 0;
}
