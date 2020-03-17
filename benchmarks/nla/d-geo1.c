/* 
Geometric Series
computes x=(z-1)* sum(z^k)[k=0..k-1] , y = z^k
returns 1+x-y == 0
*/

int vloop(int x, int y, int z, int k, int c) {
    vtrace1(x,y, z, k, c);
    int bnd = 500;
    int counter = 0;

    while (c<k) {
	if (counter >= bnd)
            break;
        else
            counter++;
        vtrace2(x, y, z, k, c);

        //__VERIFIER_assert(x*z - x - y + 1 == 0);

        c = c + 1;
        x = x * z + 1;
        y = y * z;

    }
    if (counter < bnd) {
        vtrace3(x,y, z, k, c);
    }
}

void mainQ(int z, int k) {
    int x, y, c;

    x = 1;
    y = z;
    c = 1;

    vloop(x, y, z, k, c);

    //x = x * (z - 1);

    //__VERIFIER_assert(1 + x - y == 0);
    //return 0;
}


void main(int argc, char **argv){
  mainQ(atoi(argv[1]), atoi(argv[2]));
}
