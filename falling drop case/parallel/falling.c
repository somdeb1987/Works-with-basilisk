#include "navier-stokes/centered.h"
#include "vof.h"
#include "tension.h"
//~ #include "green-naghdi.h"

#define D0 			0.0018
#define V0 			1.8
#define G			9.81
#define REYNOLDS       		324 
#define We 			135
#define H 			10*D0
#define pool_depth 		4*D0
#define height			0.0001*D0

#define rho1 			1.2
#define mu1 			1.98e-5

#define r0			0.5*D0
#define rho2 			918.
#define mu2	       		rho2*V0*r0/REYNOLDS 
#define SIGMA			rho2*V0*V0*r0/We



#define LEVEL 10

scalar f[];
scalar * interfaces = {f};
face vector alphav[];
scalar rhov[];
face vector muv[];

u.t[right]  = dirichlet(0);
uf.t[right] = dirichlet(0);
u.t[left]   = dirichlet(0);
uf.t[left]  = dirichlet(0);

uf.n[top]    = 0;
uf.n[bottom] = 0;
p[top]       = neumann(0);
p[bottom]    = neumann(0);


int main() {
//  L0=H;
//  N=512;
//  G = 1.0;
  size(H);
  init_grid (1<<LEVEL);
  
  alpha = alphav;
  rho = rhov;
  mu = muv;
  f.sigma = SIGMA;
  TOLERANCE = 1e-4;
  run();
}

event init (t = 0) {
  vertex scalar phi1[];
  vertex scalar phi2[];
  vertex scalar phi[];
  foreach_vertex(){
    phi1[] = sq(x - 0.5*H) + sq(y - (pool_depth + D0 * 0.5 + height)) - sq(D0 * 0.5);
    phi2[]=y-pool_depth;
		 }
  foreach_vertex()
     phi[] = min(phi1[],phi2[]);
  fractions (phi, f);
 
  foreach() 
	if (phi[] == phi1[]) 
		u.y[]=-1.0;
	
  
  FILE * fp = fopen ("log.dat" , "w" );
  fprintf (fp, "%d %g \n", i, t);
  fclose(fp);
  
  scalar omega[];
  vorticity (u, omega);
  FILE * fp1 = fopen ("Vorticity", "w");
  output_field ({omega}, fp1, linear = true);
  fclose (fp1);
}
event acceleration (i++) {
  face vector av = a;
  foreach_face(x)
    av.y[] -= G;
}
#define rho(f) ((f)*rho1 + (1. - (f))*rho2)
#define mu(f)  ((f)*mu1 + (1. - (f))*mu2)

event properties (i++) {
  foreach_face() {
    double ff = (f[] + f[-1])/2.;
    alphav.x[] = fm.x[]/rho(ff);
    muv.x[] = fm.x[]*mu(ff);
  }
  foreach()
    rhov[] = cm[]*rho(f[]);
}

event adapt (i++) {
  double uemax = 1e-2;
  adapt_wavelet ({f,u}, (double[]){0.01,uemax,uemax}, LEVEL, 8);
}

event logfile (i++) {
  double xb = 0., vb = 0., sb = 0.;
  foreach(reduction(+:xb) reduction(+:vb) reduction(+:sb)) {
    double dv = (1. - f[])*dv();
    xb += x*dv;
    vb += u.x[]*dv;
    sb += dv;
  }
  printf ("%g %g %g %g %g %g %d %d %d\n", 
	  t, sb, -1., xb/sb, vb/sb, dt, mgp.i, mgpf.i, mgu.i);
	  
  FILE * fp = fopen ("log.dat" , "a" );
  fprintf (fp, "%d %g \n", i, t);
  fclose(fp);
  
  scalar omega[];
  vorticity (u, omega);
  FILE * fp1 = fopen ("Vorticity", "w");
  output_field ({omega}, fp1, linear = true);
  fclose (fp1);
  
  FILE * fp2 = fopen ("mu.dat" , "w" );
  output_field ({muv}, fp2, linear = true);
  fclose (fp2);
  
  FILE * fp3 = fopen ("rho.dat" , "w" );
  output_field ({rhov}, fp3, linear = true);
  fclose (fp3);
  
  FILE * fp4 = fopen ("st.dat" , "w" );
  output_field ({f}, fp4, linear = true);
  fclose (fp4);
  //~ 
  FILE * fp5 = fopen ("alpha.dat" , "w" );
  output_field ({alphav}, fp5, linear = true);
  fclose (fp5);
  //~ 
}
event interface (t = 1.) {
  output_facets (f, stderr);
}

event movies (i += 2; t <= 15.) {
  static FILE * fp1 = popen ("ppm2mpeg > f.mpg", "w");
  output_ppm (f, fp1, box = {{0.0,0.0},{0.5*H,H}},
	      linear = true, min = 0, max = 1);
      
  static FILE * fp = popen ("ppm2mpeg > vort.mpg", "w");
  scalar omega[];
  vorticity (u, omega);
  output_ppm (omega, fp, box = {{0.0,0.0},{10*D0,10*D0}},
	      linear = true, min = 0, max = 1);
}

