struct Matrix {
    A: [[Float; 2]; 2],
    rows: u32,
    cols: u32,
    _LU: ([[Float; 2]; 2], [Float; 2])
}

impl Matrix {
    fn new(a: [[Float; 2]; 2]) -> Matrix {
        Matrix {
            A: a,
            rows: 2,
            cols: 2,
            _LU: ([[Float::with_val(53, 0.0); 2]; 2], [Float::with_val(53, 0.0); 2])
        }
    }
}



fn jacobian(f: fn(Complex) -> [[Float; 2]; 2], x: Matrix) {
    let h = eps.sqrt();
    let fx = f(*x);
    let m = fx.len();
    let n = x.len();
    let mut J = [[0; m]; n];
    for j in 0..n {
        let mut xj = x.clone();
        xj[j] += h;
        Jj = (f(*xj) - fx) / h;
        for i in 0..m {
            J[i][j] = Jj[i];
        }
    }
    return J;
}



fn LU_decomp(A: [[Float; 2]; 2]) -> ([[Float; 2]; 2], [Float; 2]) {
    let overwrite = false;
    let use_cache = true;
    /*
    if A.rows != A.cols {
        panic!("need n*n matrix");
    }
    */
    if use_cache && A._LU {
        return A._LU;
    }
    let orig;
    let Acopy;
    if !overwrite {
        orig = A;
        Acopy = A.clone();
    } else {
        Acopy = A;
    }
    tol = (mnorm(Acopy, 1) * eps).abs();
    let n = 2;
    let mut p = [Special::Infinity; n - 1];
    for j in 0..(n - 1) {
        biggest = 0;
        for k in j..n {
            s = Float::with_val(prec, 0.0);
            for l in j..n {
                s += Acopy[k][l].abs();
            }
            if s.abs() <= tol {
                panic!("ZeroDivisionErrormatrix is numerically singular.");
            }
            current = 1/s * Acopy[k][j].abs();
            if current > biggest {
                biggest = current;
                p[j] = k;
            }
        }
        if p[j].is_infinite() {
            panic!("ZeroDivisionError, matrix is numerically singular.");
        }
        swap_row(Acopy, j, p[j]);
        if Acopy[j][j].abs() <= tol {
            panic!("ZeroDivisionError matrix is numerically singular");
        }
        for i in (j + 1)..n {
            Acopy[i][j] /= Acopy[j][j];
            for k in (j + 1)..n {
                Acopy[i][k] -= Acopy[i][j] * Acopy[j][k];
            }
        }
    }
    /*
    if p && Acopy[n - 1][n - 1].abs() <= tol {
        panic!("ZeroDivisionError, matrix is numerically singular");
    }
    */
    if !overwrite {
        orig._LU = (Acopy, p);
    }
    return (Acopy, p);
}

fn L_solve(L: [[Float; 2]; 2], b: [Float; 2], p: [Float; 2]) {
    let n = 2;
    b = b.clone();
    if p {
        for k in 0..p.len() {
            swap_row(b, k, p[k]);
        }
    }
    for i in 1..n {
        for j in 0..i {
            b[i] -= L[i][j] * b[j];
        }
    }
    return b;
}

fn U_solve(U: [[Float; 2]; 2], y: [Float; 2]) {
    let n = 2;
    let mut x = y.clone();
    for i in ((n - 1)..-1).step_by(-1) {
        for j in (i + 1)..n {
            x[i] -= U[i][j] * x[j];
        }
        x[i] /= U[i][i];
    }
    return x;
}


fn lu_solve(A: [[Float; 2]; 2], b: [Float; 2]) {
    //prec = ctx.prec;
    prec += 10;
    let mut Acopy = A.clone();
    let mut bcopy = b.clone();
    if Acopy.rows < Acopy.cols {
        panic!("cannot solve underdetermined system.");
    }
    let x;
    /*
    if Acopy.rows > Acopy.cols {
        let AH = Acopy.H;
        Acopy = AH * Acopy;
        bcopy = AH * bcopy;
        x = cholesky_solve(Acopy, bcopy);
    } else {
    */
    let p;
    (Acopy, p) = LU_decomp(Acopy);
    bcopy = L_solve(Acopy, bcopy, p);
    x = U_solve(Acopy, bcopy);
    //}
    x.set_prec(prec);
    return x;
}


struct MDNewton {
    step: i32,
    maxsteps: i32,
    converged: bool, 
    f: fn(Complex) -> Complex,
    x0: Complex,
    J: fn(Matrix) -> Complex,
    tol: f64,
    verbose: bool,
    method: FindRootMethod,
    queue: VecDeque<(Matrix, Float)>,
}

impl MDNewton {
    fn new(f: fn(Complex) -> [[Float; 2]; 2], x0: Complex, norm: Fn(Complex) -> Float) -> MDNewton {
        MDNewton {
            f: f,
            x0: Matrix(x0),
            J: move |x| { jacobian(f, x) },
            norm: norm,
            verbose: false,
            converged: false,
            step: 0,
            maxsteps: 10,
            method: FindRootMethod::Mdnewton,
            queue: VecDeque::with_capacity(10),
        }
    }
    
    fn iter(&mut self) {
        let f = self.f;
        let mut x0 = self.x0;
        let norm = self.norm;
        let J = self.J;
        let mut fx = f(*x0);
        let mut fxnorm = norm(fx);
        self.converged = false;
        loop {
            let fxn = -fx;
            let Jx = J(*x0);
            let s = lu_solve(Jx, fxn);
            if self.verbose {
                println!("Jx: {}", Jx);
                println!("s: {}", s);
            }
            let mut l = one;
            let mut x1 = x0 + s;
            loop {
                if x1 == x0 {
                    if self.verbose {
                        println!("Canceled, won 't get more exact.");
                    }
                    self.converged = true;
                    break;
                }
                fx = f(*x1);
                let newnorm = norm(fx);
                if newnorm < fxnorm {
                    fxnorm = newnorm;
                    x0 = x1;
                    break;
                }
                l /= 2;
                x1 = x0 + l * s;
            }
            queue.push_back((x0, fxnorm));
            if self.converged {
                break;
            }
        }
    }
}

