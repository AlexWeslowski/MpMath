use core::cmp::max;
use core::cmp::min;
use core::cmp::Ordering;
use core::ptr::NonNull;
use fastapprox::fast::lambertw;
//use gmp_mpfr_sys::gmp::limb_t;
//use gmp_mpfr_sys::mpfr::{mpfr_t, prec_t};
use lazy_static::lazy_static; // 1.4.0
use num_traits::Pow;
use rug::Complex;
use rug::Float;
use rug::float::Special;
use rug::Integer;
use rug::integer::ImmutablePower;
use rug::Rational;
use std::boxed::Box;
use std::collections::HashMap;
use std::collections::Vec;
use std::collections::VecDeque;
use std::sync::Mutex;


const math_pi: f64 = 3.141592653589793;
const NPY_PI: f64 = 3.141592653589793;

lazy_static! {
    static ref pi_cache: Mutex<HashMap<u32, Float>> = Mutex::new(HashMap::new());
    static ref e_cache: Mutex<HashMap<u32, Float>> = Mutex::new(HashMap::new());
}

//let round_fast = Round::Down;

fn pi(prec: u32) -> Float {
    let cache: HashMap<u32, Float> = pi_cache.lock().unwrap();
    if !cache.contains_key(&prec) {
        cache.insert(prec, Float::with_val(prec, -1.0).acos());
    }
    return cache[&prec];
}

fn e(prec: u32) -> Float {
    let cache: HashMap<u32, Float> = e_cache.lock().unwrap();
    if !cache.contains_key(&prec) {
        cache.insert(prec, Float::with_val(prec, 1.0).exp());
    }
    return cache[&prec];
}

fn bernoulli_size(n: i64) -> u32 {
    let nlog2 = (n as f64).log2();
    return (2.326 + 0.5*nlog2 + (n as f64)*(nlog2 - 4.094)).round() as u32;
}

// 
// https://github.com/mpmath/mpmath/blob/master/mpmath/libmp/gammazeta.py#L464
// 
fn bernfrac(n: i64, prec: u32) -> Rational {
    let bplus = false;
    if n < 3 {
        return match n {
            0 => Rational::from((1, 1)),
            1 => if bplus { Rational::from((1, 2)) } else { Rational::from((-1, 2)) },
            2 => Rational::from((1, 6)),
        }
    }
    if n % 2 == 1 {
        return Rational::from((0, 1));
    }
    let mut q = Integer.from(1);
    for k in list_primes(n+1) {
        if !(n % (k-1)) {
            q *= k;
        }
    }
    prec = bernoulli_size(n) + ((q as Float).log2().round() as u32) + 20;
    let p = mpf_bernoulli(n, prec) * q;
    return Rational::from((p.to_integer(), q));
}
    
fn mpf_bernoulli_huge(n: i64, prec: u32) -> Float {
    let wp = prec + 10;
    let fltn = Float::with_val(wp, n);
    let piprec = wp + (fltn.log2() as u32);
    let mut v = Float::with_val(wp, Float::factorial(n + 1.0));
    v = v * fltn.zeta();
    v = v * Pow::pow(pi(piprec), -fn);
    v = v >> (1 - n);
    if !(n & 3) {
        v = -v;
    }
    v.set_prec(prec);
    return v;
}

const MAX_BERNOULLI_CACHE: u32 = 3000;
lazy_static! {
    static ref bernoulli_cache: Mutex<HashMap<u32, (HashMap<i64, Float>, (i64, i64, i64))>> = Mutex::new(HashMap::new());
}

fn mpf_bernoulli(n: i64, prec: u32) -> Float {
    let bplus = false;
    if n < 2 {
        if n == 0 {
            return Float::with_val(prec, 1.0);
        }
        if n == 1 {
            if bplus { 
                return Float::with_val(prec, 0.5);
            } else { 
                return Float::with_val(prec, -0.5);
            };
        }
    }
    if n % 2 == 1 {
        return 0;
    }
    if prec > MAX_BERNOULLI_CACHE && prec as f64 > (bernoulli_size(n) as f64) * 1.1 + 1000.0 {
        return bernfrac(n, prec);
    }
    if n > MAX_BERNOULLI_CACHE as i64 {
        return mpf_bernoulli_huge(n, prec);
    }
    let mut wp = prec + 30;
    wp += 32 - (prec & 31);
    let mut numbers;
    let mut state;
    let mut m;
    let mut bin;
    let mut bin1;
    if bernoulli_cache.contains_key(&wp) {
        (numbers, state) = bernoulli_cache[&wp];
        if numbers.contains_key(&n) {
            numbers[&n].set_prec(prec);
            return numbers[&n];
        }
        (m, bin, bin1) = state;
        if n - m > 10 {
            return mpf_bernoulli_huge(n, prec);
        }
    } else {
        if n > 10 {
            return mpf_bernoulli_huge(n, prec);
        }
        numbers = HashMap::from([(0, Float::with_val(prec, 1.0))]);
        state = (2, 10, 1);
        (m, bin, bin1) = state;
        bernoulli_cache.insert(wp, (numbers, state));
    }
    while m <= n {
        let case = m % 6;
        let szbm = bernoulli_size(m);
        let mut s = Float::with_val(prec, 0.0);
        let sexp = core::cmp::max(0, szbm) - wp;
        let mut a = if m < 6 { 0 } else { bin1 };
        for j in 1..(m/6+1) {
            let usign = numbers[&(m-6*j)].signum();
            let mut uman = numbers[&(m-6*j)].get_significand().unwrap();
            let uexp = numbers[&(m-6*j)].get_exp().unwrap();
            let ubc = numbers[&(m-6*j)].prec();
            if using == 1 {
                uman = -uman;
            }
            s += Float::with_val(prec, a * uman) << (uexp - sexp);
            let j6 = 6*j;
            a *= (m-5-j6)*(m-4-j6)*(m-3-j6)*(m-2-j6)*(m-1-j6)*(m-j6);
            a /= (4+j6)*(5+j6)*(6+j6)*(7+j6)*(8+j6)*(9+j6);
        }
        let mut b = match case {
            0 => Float::with_val(prec, m+3) / Float::with_val(prec, 3),
            2 => Float::with_val(prec, m+3) / Float::with_val(prec, 3),
            4 => Float::with_val(prec, -m-3) / Float::with_val(prec, 6),
        };
        s = s * Pow::pow(2, sexp);
        b = (b - s) / bin;
        numbers.insert(m, b);
        m += 2;
        bin = bin * ((m+2)*(m+3)) / (m*(m-1));
        if m > 6 {
            bin1 = bin1 * ((2+m)*(3+m)) / ((m-7)*(m-6));
        }
        state = (m, bin, bin1);
    }
    return numbers[&n];
}


fn mpf_cos_sin_pi(x: Float, prec: u32) -> (Float, Float) {
    return mpf_cos_sin(x, true, prec);
}

const EXP_COSH_CUTOFF: u32 = 600;

// 
// https://github.com/mpmath/mpmath/blob/master/mpmath/libmp/libelefun.py#L1107
// 
fn exp_expneg_basecase(x: Float, prec: u32) -> (Float, Float) {
    if prec > EXP_COSH_CUTOFF {
        let (cosh, sinh) = exponential_series(x, 1, prec);
        return (cosh + sinh, cosh - sinh);
    }
    let a = x.exp();
    let b = (Complex::with_val(prec + prec, (1.0, 0.0)) << (prec + prec)) / a;
    return (a, b);
}

// 
// https://github.com/mpmath/mpmath/blob/master/mpmath/libmp/libelefun.py#L1192
// 
fn mpf_cosh_sinh(x: Float, prec: u32) -> (Float, Float) {
    sign = x.signum();
    man = x.get_significand().unwrap();
    exp = x.get_exp().unwrap();
    bc = x.prec();
    if !man && exp {
        /*
        if tanh {
            if x == finf {
                return fone;
            }
            if x == fninf {
                return fnone;
            }
            return fnan
        }
        */
        if x.is_infinite() && sign == 1 {
            return (Float::with_val(prec, Special::Infinity), Float::with_val(prec, Special::Infinity));
        }
        if x.is_infinite() && sign == -1 {
            return (Float::with_val(prec, Special::Infinity), Float::with_val(prec, Special::NegInfinity));
        }
        return (Float::with_val(prec, Special::Nan), Float::with_val(prec, Special::Nan));
    }
    let mag = exp + bc;
    let mut wp = prec + 14;
    if mag < -4 {
        if mag < -(wp as i32) {
            /*
            if tanh:
                return mpf_perturb(x, 1-sign, prec, rnd)
            */
            return (mpf_perturb(Float::with_val(prec, 1.0), 0, prec, rnd), mpf_perturb(x, sign, prec, rnd));
        }
        wp += -mag;
    }
    if mag > 10 {
        if 3 * (1 << (mag - 1)) > wp {
            /*
            if tanh:
                return mpf_perturb([fone,fnone][sign], 1-sign, prec, rnd)
            */
            x = x.abs();
            x.exp_round(Round::Down);
            c = x >> -1;
            if sign {
                s = -c;
            } else {
                s = c;
            }
            return (c, s);
        }
    }
    let offset;
    if mag > 1 {
        let wpmod = wp + mag;
        offset = exp + wpmod;
        if offset >= 0 {
            t = man << offset;
        } else {
            t = man >> (-offset);
        }
        let log2 = (wpmod as f32).log2();
        n = (t / log2).to_integer().unwrap();
        t = t % log2;
        t >>= mag;
    } else {
        offset = exp + wp;
        if offset >= 0 {
            t = man << offset;
        } else {
            t = man >> (-offset);
        }
        n = 0;
    }
    (a, b) = exp_expneg_basecase(t, wp);
    cosh = a + (b>>(2*n));
    sinh = a - (b>>(2*n));
    if sign {
        sinh = -sinh;
    }
    /*
    if tanh:
        man = (sinh << wp) // cosh
        return from_man_exp(man, -(wp as i32), prec);
    else:
    */
    return (from_man_exp(cosh, n - (wp as i32) - 1, prec), from_man_exp(sinh, n - (wp as i32) - 1, prec));
}

// 
// https://github.com/mpmath/mpmath/blob/master/mpmath/libmp/libmpc.py#L491
// 
fn mpc_cos_pi(z: Complex, prec: u32) -> Complex {
    let a = z.real();
    let b = z.imag();
    if b.is_zero() {
        a.cos_pi_round(Round::Down);
        return Complex::with_val(prec, (a, Float::with_val(prec, 0.0)));
    }
    b.set_prec(prec + 5);
    b = &(b * pi(prec + 5));
    if a.is_zero() {
        b.cosh_round(Round::Down);
        return Complex::with_val(prec, (b, Float::with_val(prec, 0.0)));
    }
    let wp = prec + 6;
    let (c, s) = mpf_cos_sin_pi(a.clone(), wp);
    let (ch, sh) = mpf_cosh_sinh(b.clone(), wp);
    return Complex::with_val(prec, (c * ch, s * sh));
}


// 
// https://github.com/mpmath/mpmath/blob/master/mpmath/libmp/libmpc.py#L505
// 
fn mpc_sin_pi(z: Complex, prec: u32) -> Complex {
    a = z.real();
    b = z.imag();
    if b.is_zero() {
        return Complex::with_val(prec, (a.sin_pi_round(Round::Down), Float::with_val(prec, 0.0)));
    }
    b.set_prec(prec + 5);
    b = b * pi(prec + 5);
    if a.is_zero() {
        return Complex::with_val(prec, (Float::with_val(prec, 0.0), b.sinh_round(Round::Down)));
    }
    let wp = prec + 6;
    let (c, s) = mpf_cos_sin_pi(a, wp);
    let (ch, sh) = mpf_cosh_sinh(b, wp);
    return Complex::with_val(prec, (s * ch, c * sh));
}


// 
// https://github.com/mpmath/mpmath/blob/master/mpmath/libmp/gammazeta.py#L701
// 
fn mpc_digamma(mut z: Complex, prec: u32) -> Complex {
    let re = z.real();
    let im = z.imag();
    if im.is_zero() {
        return Complex::with_val(prec, (re.digamma(), Float::with_val(prec, 0.0)));
    }
    let wp = prec + 20;
    z.set_prec(wp);
    let sign = re.signum();
    let man = re.get_significand().unwrap();
    let exp = re.get_exp().unwrap();
    let bc = re.prec() as i32;
    let mut s;
    if sign == 1 && exp + bc > 3 {
        let c = mpc_cos_pi(z, wp);
        s = mpc_sin_pi(z, wp);
        q = (c / s) * pi(wp);
        p = mpc_digamma(Complex::with_val(wp, (1.0, 0.0)) - z, wp);
        s = p - q;
        s.set_prec(prec);
        return s;
    }
    if sign == 0 && bc + exp > wp {
        s = (z - Complex::with_val(wp, (1.0, 0.0))).ln();
        s.set_prec(prec);
        return s;
    }
    let w = re.to_integer().unwrap().to_i64().unwrap();
    let n = (0.11 * (wp as f32)) as i64 + 2;
    s = Complex::with_val(wp, (0.0, 0.0));
    if w < n {
        for k in w..n {
            s = s - 1.0 / z;
            z = z + Complex::with_val(wp, (1.0, 0.0));
        }
    }
    z = z - Complex::with_val(wp, (1.0, 0.0));
    s = s + z.ln();
    s = s + Complex::with_val(wp, (0.5, 0.0)) / z;
    let z2 = z * z;
    let mut t = Complex::with_val(wp, (1.0, 0.0));
    let mut prev = Float::with_val(wp, 0.0);
    let mut szprev = 0.0;
    k = 1;
    eps = Float::with_val(wp, 1.0) << (-(wp as i32) + 2);
    loop {
        t = t * z2;
        let term = mpf_bernoulli(2*k, wp) / (t * 2 * k);
        s = s - term;
        term.set_prec(10);
        szterm = term.abs();
        if k > 2 && szterm <= eps || szprev <= szterm {
            break;
        }
        prev = term;
        szprev = szterm;
        k += 1;
    }
    return s;
}


fn mpc_polygamma(mut m: i64, mut z: Complex, prec: u32) -> Complex {
    if m == 0 {
        return mpc_digamma(z, prec);
    }
    let re = z.real();
    let im = z.imag();
    let wp = prec + 20;
    z.set_prec(wp);
    let sign = re.signum();
    let man = re.get_significand().unwrap();
    let exp = re.get_exp();
    let bc = re.prec();
    if im.is_infinite() || im.is_nan() {
        return (Float::with_val(prec, Special::Nan), Float::with_val(prec, Special::Nan));
    }
    if !man {
        if re.is_infinite() && im.is_zero() {
            return (Float.with_val(prec, 0), Float.with_val(prec, 0));
        }
        if re.is_nan() {
            return (Float::with_val(prec, Special::Nan), Float::with_val(prec, Special::Nan));
        }
    }
    let w = re.to_integer();
    let n = ((0.4*(wp as f64) + 4*m).round() as i64);
    let mut s = Float.with_val(wp, 0.0);
    if w < n {
        for k in w..n {
            let t = Pow::pow(z, -m-1);
            s = s + t;
            z = z + Float::with_val(wp, 1.0);
        }
    }
    let mut zm = Pow::pow(z, -m);
    zm.set_prec(wp);
    let z2 = 1.0 / (z * z);
    # 1/m*(z+N)^m
    let integral_term = zm / Float.with_val(wp, m);
    s = s + integral_term;
    # 1/2*(z+N)^(-(m+1))
    s = s + (zm / z) * Float::with_val(wp, 0.5);
    let mut a = m + 1;
    let mut b = 2;
    let mut k = 1;
    let magn = s.abs();
    magn.set_prec(10);
    let magn = magn.get_exp() + magn.prec();
    let eps = Float::with_val(wp, 1.0) >> (magn - wp + 2);
    loop {
        zm = zm * z2;
        zm.set_prec(wp);
        let bern = mpf_bernoulli(2*k, wp);
        let mut scal = bern * Float::with_val(wp, a as f64);
        scal = scal / Float.with_val(wp, b);
        let term = zm * scal;
        s = s + term;
        let mut szterm = term.abs();
        szterm.set_prec(10);
        if k > 2 && szterm <= eps {
            break;
        }
        a *= (m+2*k)*(m+2*k+1);
        b *= (2*k+1)*(2*k+2);
        k += 1;
    }
    v = s * Float::with_val(wp, m + 1).gamma();
    v.set_prec(prec);
    if !(m & 1) {
        *v.mut_real() = -v.real();
        *v.mut_imag() = -v.imag();
    }
    return v;
}


//
// https://github.com/mpmath/mpmath/blob/master/mpmath/libmp/gammazeta.py#L1887 
// 
fn mpc_gamma(z: Complex, utype: u32, prec: u32) -> Complex {
    let mut a = z.real();
    let mut b = z.imag();
    let mut asign = a.signum();
    let mut aman = a.get_significand().unwrap();
    let mut aexp = a.get_exp().unwrap();
    let mut abc = aman.significant_bits();
    let mut bsign = b.signum();
    let mut bman = b.get_significand().unwrap();
    let mut bexp = b.get_exp().unwrap();
    let mut bbc = bman.significant_bits();
    
    if b.is_zero() {
        // todo: check if is_sign_positive() is correct
        if utype == 3 && a.is_sign_positive() {
            a.ln_gamma_round(Round::Down);
            let n = (-aman) >> (-aexp)
            let im = pi(prec + 10) * n;
            return Complex::with_val(prec, (a, im));
        }
        return Complex::with_val(prec, (mpf_gamma(a, utype, prec), 0.0));
    }
    
    if (aman.is_zero() && !aexp.is_zero()) || (bman.is_zero() && !bexp.is_zero()) {
        return Complex::with_val(prec, (Special::Nan, Special::Nan));
    }
    
    let wp = prec as i32 + 20;
    let amag = aexp + abc;
    let bmag = bexp + bbc;
    if !aman.is_zero() {
        mag = max(amag, bmag);
    } else {
        mag = bmag;
    }
    
    if mag < -8 {
        if mag < -wp {
            z.set_prec(wp);
            let v = z + z * z * euler_fixed(wp);
            if utype == 0 {
                v = 1 / v;
            } else if utype == 1 {
                v = z / v;
            } else if utype == 2 {
                // v = mpc_pos(v);
            } else if utype == 3 {
                v = 1 / v;
                v.ln_round(Round::Down);
            }
            v.set_prec(prec);
            return v;
        } else if utype != 1 {
            wp += (-mag)
        }
    }
    
    if utype == 3 && mag > wp && (!a.is_sign_positive() || bmag >= amag) {
        return mpc_sub(mpc_mul(z, mpc_log(z, wp), wp), z, prec, rnd)
    }
    
    if utype == 1 {
        return mpc_gamma(Complex::with_val(prec, (a + Float::with_val(prec, 1.0), b)), 0, prec);
    }
    
    let an = a.to_integer().abs();
    let bn = b.to_integer().abs();
    let absn = max(an, bn);
    let gamma_size = absn * mag;
    if utype == 3 {
        pass;
    } else {
        wp += gamma_size.bit_length();
    }
    
    need_reflection = a.is_sign_positive();
    let zorig = z;
    if need_reflection {
        z = -z;
        a = z.real();
        asign = a.signum();
        aman = a.get_significand().unwrap();
        aexp = a.get_exp().unwrap();
        abc = aman.significant_bits();
        b = z.real();
        bsign = b.signum();
        bman = b.get_significand().unwrap();
        bexp = b.get_exp().unwrap();
        bbc = bman.significant_bits();
    }
    
    let mut yfinal = 0;
    let balance_prec = 0;
    if bmag < -10 {
        if utype == 3 {
            let zsub1 = z - Float::with_val(wp, 1.0);
            let cancel1;
            if zsub1.real().is_zero() {
                cancel1 = -bmag;
            } else {
                cancel1 = -max(zsub1.real().get_exp().unwrap() + zsub1.real().get_significand().unwrap().significant_bits(), bmag);
            }
            if cancel1 > wp {
                zsub1.set_prec(wp);
                let x = zsub1 * pi(wp);
                x = x * x;
                x = x / 12;
                let y = zsub1 * -euler_fixed(wp);
                yfinal = x + y;
                if !need_reflection {
                    return mpc_pos(yfinal, prec, rnd);
                }
            } elif cancel1 > 0 {
                wp += cancel1;
            }
            zsub2 = z - Float::with_val(prec, 2.0);
            let cancel2;
            if zsub2.real().is_zero() {
                cancel2 = -bmag;
            } else {
                cancel2 = -max(zsub2.real().get_exp().unwrap() + zsub2.real().get_significand().unwrap().significant_bits(), bmag);
            }
            if cancel2 > wp {
                t = pi(wp) * pi(wp) - 6;
                zsub2.set_prec(wp);
                x = zsub2 * zsub2 * t;
                x = x / 12;
                y = zsub2 * (Float::with_val(wp, 1.0) - euler_fixed(wp));
                yfinal = x + y;
                if !need_reflection {
                    yfinal.set_prec(prec);
                    return mpc_pos(yfinal);
                }
            } else if cancel2 > 0 {
                wp += cancel2
            }
        }
        if bmag < -wp {
            let pp = 2 * (wp + 10);
            let mut aabs = a.abs();
            aabs.set_prec(pp);
            let eps = Float::with_val(amag, 1.0) >> (amag-wp);
            let x1 = mpf_gamma(aabs, pp, utype);
            let x2 = mpf_gamma(aabs + eps, pp, utype);
            let xprime = mpf_div(mpf_sub(x2, x1, pp), eps, pp);
            let y = b * xprime;
            yfinal = (x1, y);
            if !need_reflection {
                yfinal.set_prec(prec);
                return mpc_pos(yfinal);
            }
        } else {
            balance_prec += -bmag;
        }
    }
    
    wp += balance_prec;
    let n_for_stirling = int(GAMMA_STIRLING_BETA*wp)
    let need_reduction = absn < n_for_stirling;
    let afix = to_fixed(a, wp);
    let bfix = to_fixed(b, wp);
    let mut r = 0;
    if !yfinal {
        let zprered = z;
        if absn < n_for_stirling {
            absn = complex(an, bn)
            let d = int((1 + n_for_stirling**2 - bn**2)**0.5 - an)
            let mut rre = one = MPZ_ONE << wp
            let mut rim = Complex::with_val(wp, (0.0, 0.0));
            for k in 0..d {
                (rre, rim) = ((afix*rre-bfix*rim)>>wp), ((afix*rim + bfix*rre)>>wp);
                afix += one;
            }
            r = from_man_exp(rre, -wp), from_man_exp(rim, -wp);
            a = from_man_exp(afix, -wp);
            z = a, b;
        }
        yre, yim = complex_stirling_series(afix, bfix, wp);
        z.set_prec(wp);
        (lre, lim) = z.ln();
        lre = to_fixed(lre, wp);
        lim = to_fixed(lim, wp);
        yre = ((lre*afix - lim*bfix)>>wp) - (lre>>1) + yre;
        yim = ((lre*bfix + lim*afix)>>wp) - (lim>>1) + yim;
        y = from_man_exp(yre, -wp), from_man_exp(yim, -wp);
        
        if r != 0 && utype == 3 {
            y = y - r.ln();
            let zfa = zprered.real().to_f64();
            let zfb = zprered.imag().to_f64();
            let zfabs = zprered.abs();
            let yfb = y.imag().to_f64();
            let u = zfb.atan2(zfa);
            let gi;
            if zfabs <= 0.5 {
                gi = 0.577216 * zfb - u;
            } else {
                gi = -zfb - 0.5 * u + zfa * u + zfb * zfabs.ln();
            }
            n = ((gi-yfb)/(2*math.pi)+0.5).floor().to_integer();
            y = Complex::with_val(wp, (y.real(), y.imag() + pi(wp) * 2 * n));
        }
    }
    
    if need_reflection {
        if utype == 0 || utype == 2 {
            let mut A = mpc_sin_pi(zorig, wp) * zorig;
            let mut B = Complex::with_val(wp, (-pi(wp), Float::with_val(wp, 0.0)));
            if yfinal {
                if utype == 2 {
                    A = mpc_div(A, yfinal, wp)
                } else {
                    A = mpc_mul(A, yfinal, wp)
                }
            } else {
                A = A * y.exp();
            }
            if r != 0 {
                B = B * r;
            }
            if utype == 0 {
                return B / A;
            }
            if utype == 2 {
                return A / B;
            }
        }
        if utype == 3 {
            if yfinal {
                s1 = mpc_neg(yfinal);
            } else {
                s1 = mpc_neg(y);
            }
            s1 = s1 - (-zorig).ln();
            rezfloor = zorig.real().floor();
            imzsign = zorig.imag().signum();
            t = pi(wp) * rezfloor;
            t = t * imzsign;
            s1 = Complex::with_val(wp, (s1.real(), s1.imag() + t));
            s1 = s1 + pi(wp).ln();
            t = mpc_sin_pi(zorig - rezfloor, wp);
            t = t.ln();
            s1 = s1 - t;
            if imzsign == 0 {
                t = pi(wp) * rezfloor.floor();
                s1 = Complex::with_val(wp, (s1.real(), s1.imag() - t));
            }
            s1.set_prec(prec);
            return mpc_pos(s1, prec);
        }
    } else {
        if utype == 0 {
            if r != 0 {
                r = y.exp() / r;
                r.set_prec(prec);
                return r;
            }
            return mpc_exp(y, prec, rnd)
        }
        if utype == 2 {
            if r != 0 {
                r = r / y.exp();
                r.set_prec(prec);
                return r;
            }
            y = -y;
            y.exp_round(Round::Down);
            y.set_prec(prec);
            return y;
        }
        if utype == 3 {
            return mpc_pos(y, prec, rnd);
        }
    }
}


// 
// https://github.com/mpmath/mpmath/blob/master/mpmath/libmp/gammazeta.py#L2139
// 
fn mpc_log_gamma(z: Complex, prec: u32) -> Complex {
    let a = z.real();
    let b = z.imag();
    let asign = a.signum();
    let aman = a.get_significand().unwrap();
    let aexp = a.get_exp().unwrap();
    let abc = aman.significant_bits();
    let bsign = b.signum();
    let bman = b.get_significand().unwrap();
    let bexp = b.get_exp().unwrap();
    let bbc = bman.significant_bits();
    if b.is_zero() && a.is_sign_positive() {
        a.ln_gamma_round(Round::Down);
        let n = (-aman) >> (-aexp);
        let im = pi(prec+10) * n;
        return Complex::with_val(prec, (a, im));
    }
    return mpc_gamma(z, 3, prec);
}

fn mpc_pow(z: Complex, w: Complex, prec:u32) {
    if w.imag().is_zero() {
        return mpc_pow_mpf(z, w.real(), prec);
    }
    z.set_prec(prec + 10);
    w.set_prec(prec + 10);
    let rtn = z.ln() * w;
    rtn.exp_round(Round::Down);
    rtn.set_prec(prec);
    return rtn;
}

fn mpc_pow_mpf(z: Complex, p: Float, prec: u32) -> Complex {
    psign = p.signum();
    pman = p.get_significand().unwrap();
    pexp = p.get_exp().unwrap();
    pbc = pman.significant_bits();
    if pexp >= 0 {
        return mpc_pow_int(z, Pow::pow(-1, psign) * (pman << pexp), prec);
    }
    if pexp == -1 {
        z.set_prec(prec + 10);
        return mpc_pow_int(z.sqrt(), Pow::pow(-1, psign) * pman, prec);
    }
    z.set_prec(prec + 10);
    p.set_prec(prec + 10);
    let rtn = z.ln() * p;
    rtn.exp_round(Round::Down);
    rtn.set_prec(prec);
    return rtn;
}

fn mpc_pow_int(z: Complex, n: Integer, prec: u32) -> Complex {
    a = z.real();
    b = z.imag();
    if !b.is_zero() {
        return Complex::with_val(prec, (a.pow(n), Float::with_val(prec, 0.0)));
    } 
    if a.is_zero() {
        v = b.pow(n);
        n %= 4;
        if n == 0 {
            return Complex::with_val(prec, (v, Float::with_val(prec, 0.0)));
        } else if n == 1 {
            return Complex::with_val(prec, (Float::with_val(prec, 0.0), v));
        } else if n == 2 {
            v.signum_mut() = -v.signum();
            return Complex::with_val(prec, (v, Float::with_val(prec, 0.0)));
        } else {
            v.signum_mut() = -v.signum();
            return Complex::with_val(prec, (Float::with_val(prec, 0.0), v));
        }
    }
    if n == 0 {
        Complex::with_val(prec, (1.0, 0.0));
    } else if n == 1 {
        return z;
    } else if n == 2 {
        return z * z;
    } else if n == -1 {
        return 1 / z;
    } else if n < 0 {
        z.set_prec(prec + 4);
        z = 1.0 / z.pow(-n);
        z.set_prec(prec);
        return z;
    }
    let asign = a.signum();
    let mut aman = a.get_significand().unwrap();
    let mut aexp = a.get_exp().unwrap();
    let abc = aman.significant_bits();
    let bsign = b.signum();
    let mut bman = b.get_significand().unwrap();
    let mut bexp = b.get_exp().unwrap();
    let bbc = bman.significant_bits();
    if asign {
        aman = -aman;
    }
    if bsign {
        bman = -bman;
    }
    let de = aexp - bexp;
    let abs_de = de.abs();
    let exact_size = n * (abs_de + max(abc, bbc));
    if exact_size < 10000 {
        if de > 0 {
            aman <<= de;
            aexp = bexp;
        } else {
            bman <<= (-de);
            bexp = aexp;
        }
        let mut z = complex_int_pow(aman, bman, n);
        *z.mut_real() = from_man_exp(z.real(), (n*aexp).to_integer(), prec);
        *z.mut_imag() = from_man_exp(z.imag(), (n*bexp).to_integer(), prec);
        z.set_prec(prec);
        return z;
    }
    z.set_prec(prec + 10);
    n.set_prec(prec + 10);
    let rtn = z.ln() * n;
    rtn.exp_round(Round::Down);
    rtn.set_prec(prec);
    return rtn;
}

fn complex_int_pow(mut a: Integer, mut b: Integer, n: Integer) -> Complex {
    let prec = max(a.prec(), b.prec());
    z = Complex::with_val(prec, (1.0, 0.0));
    while n > 0 {
        if n.is_odd() {
            *z.mut_real() = z.real() * a - z.imag() * b;
            *z.mut_imag() = z.imag() * a + z.real() * b;
            n -= 1;
        }
        a = a * a - b * b;
        b = 2 * a * b;
        n /= 2;
    }
    return z;
}

fn siegeltheta(t: Complex, derivative: i32) -> Complex {
    let prec = max(t.real().prec(), t.imag().prec());
    let d = derivative;
    if t.imag().is_zero() && t.real().is_infinite() {
        if d < 2 {
            if t.real().is_sign_negative() && d == 0 {
                return Complex::with_val(prec, (Special::NegInfinity, 0.0));
            }
            return Complex::with_val(prec, (Special::Infinity, 0.0));
        } else {
            return Complex::with_val(prec, (0.0, 0.0));
        }
    }
    if d == 0 {
        if !t.imag().is_zero() {
            let a = mpc_log_gamma(Complex::with_val(prec, (0.25, 0.5)) * t);
            let b = mpc_log_gamma(Complex::with_val(prec, (0.25, -0.5)) * t);
            return -pi(prec).ln()/2 * t - Complex::with_val(prec, (0.0, 0.5)) * (a-b);
        } else {
            if t.real().is_infinite() {
                return t;
            }
            return mpc_log_gamma(Complex::with_val(prec, (0.25, 0.5)) * t).imag() - pi(prec).ln()/2.0 * t;
        }
    } else if d > 0 {
        let a = mpc_pow_int(Complex::with_val(prec, (0.0, -0.5)), Integer::from(d-1)) * mpc_polygamma(d-1 as i64, Complex::with_val(prec, (0.25, -0.5)) * t, prec);
        let b = mpc_pow_int(Complex::with_val(prec, (0.0, 0.5)), Integer::from(d-1)) * mpc_polygamma(d-1 as i64, Complex::with_val(prec, (0.25, 0.5)) * t, prec);
        if !t.imag().is_zero() {
            if d == 1 {
                return Complex::with_val(prec, (-0.5 * pi(prec).ln() + 0.25 * (a + b), 0.0));
            } else {
                return Complex::with_val(prec, (0.25 * (a + b), 0.0));
            }
        } else {
            if d == 1 {
                return Complex::with_val(prec, ((-0.5 * pi(prec).ln() + 0.25 * (a + b)).real(), 0.0));
            } else {
                return Complex::with_val(prec, ((0.25 * (a + b)).real(), 0.0));
            }
        }
    }
}

fn wpzeros(t: f64) -> u32 {
    let mut wp = 53;
    if t > 3 * Pow::pow(10, 8) {
        wp = 63;
    } 
    if t > Pow::pow(10, 11) {
        wp = 70;
    }
    if t > Pow::pow(10, 14) {
        wp = 83;
    }
    return wp;
}

fn comp_fp_tolerance(n: i64) -> (f64, f64) {
    let wpz = wpzeros((n as f64) * (n as f64).ln());
    let mut fp_tolerance;
    if n < 15 * Pow::pow(10, 8) {
        fp_tolerance = 0.0005;
    } elif n <= Pow::pow(10, 14) {
        fp_tolerance = 0.1;
    } else {
        fp_tolerance = 100.0;
    }
    return (wpz, fp_tolerance);
}

fn lambertw_scalar(z: Complex, k: i64, tol: f64) -> Complex {
    if z.real().is_nan() {
        return z;
    }
    if z.imag().is_nan() {
        return z;
    }
    let prec = max(z.real().prec(), z.imag().prec());
    let mut w;
    let u = Float::with_val(prec, -1.0).exp();
    let absz = z.abs().real();
    if absz <= u {
        if z == 0 {
            if k == 0 {
                return z;
            }
            return Complex::with_val(prec, (Special::NegInfinity, 0));
        }
        if k == 0 {
            w = z; 
        } else if k == -1 && z.imag().is_zero() && z.real() < 0.0 {
            w = z.real();
            *w.signum_mut() = -w.signum();
            w = w.ln();
        } else {
            w = z.ln();
            if k != 0 {
                w = w + k * 2.0 * NPY_PI * Complex::with_val(prec, (0.0, 1.0));
            }
        }
    } else if k == 0 && !z.imag().is_zero() && z.abs().real() <= 0.7 {
        if (z + 0.5).abs() < 0.1 {
            if z.imag() > 0.0 {
                w = Complex::with_val(prec, (0.7, 0.7));
            } else {
                w = Complex::with_val(prec, (0.7, -0.7));
            }
        } else {
            w = z;
        }
    } else {
        if z.real().is_infinite() {
            if k == 0 {
                return z;
            } else {
                return z + 2.0 * k * NPY_PI * Complex::with_val(prec, (0, 1.0));
            }
        }
        if z.real().signum() == -1 && z.real().is_infinite() {
            return (-z) + (2.0 * k + 1.0) * NPY_PI * Complex::with_val(prec, (0, 1.0));
        }
        w = z.ln();
        if k != 0 {
             w = w + k * 2.0 * NPY_PI * Complex::with_val(prec, (0, 1.0));
        }
    }
    for i in 0..100 {
        let ew = w.exp();
        let wew = w * ew;
        let wewz = wew - z;
        let wn = w - wewz / (wew + ew - (w + 2) * wewz / (2 * w + 2));
        if (wn - w).abs() < tol * wn.abs() {
            return wn;
        } else {
            w = wn;
        }
    }
    //lambertw_raise_warning(z)
    //panic!("lambertw_scalar({}, {})", z, k);
    return wn;
}

// 
// https://github.com/mpmath/mpmath/blob/master/mpmath/functions/functions.py#L435
// 
fn lambertw(z: Complex) -> Complex {
    let k = 0;
    let tol = 0.00000001;
    /*
    Parameters
    ----------
    z : array_like
        Input argument.
    k : int, optional
        Branch index.
    tol : float, optional
        Evaluation tolerance.
    */
    return _lambertw(z, k, tol);
}

fn grampoint(n: i32) -> Float {
    // http://mathworld.wolfram.com/GramPoint.html
    let g = 2 * pi(53) * (1 + lambertw((8.0 * n as f32 + 1.0) / (8 * e(53)))).exp();
    let z = findroot(move |t| siegeltheta(t) - pi(53) * n, g, FindRootMethod::Illinois, 0.00000001);
    return z.real();
}

fn sum_accurately(terms: Vec<Float>, check_step: u32, prec: u32, _fixed_precision: bool) -> Float {
    //prec = ctx.prec
    let extraprec = 10;
    loop {
        //prec = prec + extraprec + 5;
        let mut max_mag = Pow::pow(2, -63);
        let mut sum_mag = 0;
        //let mut s = Complex::with_val(prec + extraprec + 5, (0.0, 0.0));
        let mut s = Float::with_val(prec + extraprec + 5, 0.0);
        k = 0;
        for term in terms {
            s += term;
            if !(k % check_step) && term {
                term_mag = mag(term);
                max_mag = max(max_mag, term_mag);
                sum_mag = mag(s);
                if sum_mag - term_mag > prec {
                    break;
                }
            }
            k += 1;
        }
        cancellation = max_mag - sum_mag;
        if cancellation != cancellation {
            break;
        }
        if cancellation < extraprec || _fixed_precision {
            break;
        }
        extraprec += min(prec, cancellation);
    }
    s.set_prec(prec);
    return s;
}


// 
// https://github.com/mpmath/mpmath/blob/master/mpmath/libmp/gammazeta.py#L1034
// 
fn mpc_zeta(s: Complex, prec: u32) -> Complex {
    let rnd = Round::Down;
    let alt = 0;
    let force = false;
    let re = s.real();
    let im = s.imag();
    if im.is_zero() {
        return Complex::with_val(prec, (re.zeta(), 0.0));
    }
    
    let sabs = s.abs();
    sabs.set_prec(10);
    if !force && sabs > prec {
        panic!("mpc_zeta() NotImplementedError");
    }
    
    let wp = prec + 20;
    s.set_prec(wp);
    let r = Complex::with_val(wp, (1.0, 0.0)) - s;
    let mut rabs = r.abs();
    rabs.set_prec(10);
    let asign = rabs.signum();
    let aman = rabs.get_significand().unwrap();
    let aexp = rabs.get_eps().unwrap();
    let abc = aman.significant_bits();
    let pole_dist = -2 * (aexp + abc);
    let mut q;
    let mut y;
    if pole_dist > wp {
        if alt != 0 {
            q = Complex::with_val(wp, (wp as f32, 0.0)).ln2();
            y = q * euler_fixed(wp);
            let mut g = (q * q) >> -1;
            g = y - g;
            let mut z = r * -g
            z = z + q;
            z.set_prec(prec);
            return z;
        } else {
            r.set_prec(wp);
            q = Complex::with_val(wp, (-1.0, 0.0)) / r + euler_fixed(wp);
            q.set_prec(prec);
            return q;
        }
    } else {
        wp += max(0, pole_dist);
    }
    
    let wp2;
    if re.signum() == -1 {
        if alt != 0 {
            q = mpc_sub(mpc_one, mpc_pow(mpc_two, mpc_sub(mpc_one, s, wp), wp), wp)
            return mpc_mul(mpc_zeta(s, wp), q, prec, rnd)
        }
        s.set_prec(10 * wp);
        y = Complex::with_val(10 * wp, (1.0, 0.0)) - s;
        let mut a = mpc_gamma(y, wp);
        let b = mpc_zeta(y, wp);
        let mut c = (s >> -1).sin_pi()
        c.set_prec(wp);
        let rsign = re.signum();
        let rman  re.get_significand().unwrap();
        let rexp  re.get_eps().unwrap();
        let rbc = rman.significant_bits();
        let isign = im.signum();
        let iman = im.get_significand().unwrap();
        let iexp = im.get_eps().unwrap();
        let ibc = iman.significant_bits();
        let mag = max(rexp + rbc, iexp + ibc);
        wp2 = wp + max(0, mag);
        let pi2 = Complex::with_val(wp + wp2, (pi(wp + wp2) >> 1, 0.0));
        let d = mpc_pow(pi2, s, wp2) / pi(wp + wp2);
        d.set_prec(wp);
        a = a * b * c * d;
        a.set_prec(prec);
        return a;
    }
    let mut n = ((wp as f32)/2.54 + 5.0) as i64;
    n += (0.9 * im.abs()) as i64;
    let d = borwein_coefficients(n);
    let ref = to_fixed(re, wp);
    let imf = to_fixed(im, wp);
    let mut tre = Complex::with_val(wp, (0.0, 0.0));
    let mut tim = Complex::with_val(wp, (0.0, 0.0));
    let one = Complex::with_val(wp, (1.0, 0.0)); << wp;
    let one_2wp = Complex::with_val(wp, (1.0, 0.0)); << (2 * wp);
    let critical_line = re == 0.5;
    let ln2 = (wp as f32).ln2();
    let pi2 = pi(wp - 1);
    let wp2 = wp + wp;
    for k in 0..n {
        let log = Float::with_val(wp, k + 1.0).ln2();
        let mut w;
        if critical_line {
            let mut kp2 = Float::with_val(wp2, (k + 1)) << wp2;
            kp2.sqrt_round(Round::Down);
            w = one_2wp / kp2;
        } else {
            w = ((-ref * log) >> wp).exp();
        }
        if k % 2 == 1 {
            w *= (d[n] - d[k]);
        } else {
            w *= (d[k] - d[n]); 
        }
        let (wre, wim) = cos_sin_fixed((-imf * log) >> wp, wp, pi2);
        tre += (w * wre) >> wp;
        tim += (w * wim) >> wp;
    }
    tre /= (-d[n]);
    tim /= (-d[n]);
    tre = from_man_exp(tre, -wp, wp);
    tim = from_man_exp(tim, -wp, wp);
    if alt {
        return Complex::with_val(prec, (tre, tim));
    } else {
        q = Complex::with_val(wp, (1.0, 0.0)) - mpc_pow(Complex::with_val(wp, (2.0, 0.0)), r, wp);
        q.set_prec(prec);
        return Complex::with_val(prec, (tre, tim)) / q;
    }
}


enum ZetaMethod {
    None,
    EulerMaclaurin,
    Borwein,
    RiemannSiegel,
    Hurwitz
}


fn zeta(s: Complex, method: ZetaMethod) -> Complex {
    let a = 1;
    let derivative = 0;
    d = derivative;
    if a == 1 && !(d != 0 || method != ZetaMethod::None) {
        return mpc_zeta(s);
    }
    //s = ctx.convert(s)
    //prec = ctx.prec
    let verbose = false;
    if s.is_zero() && derivative == 0 {
        return Float::with_val(prec, 0.5) - _convert_param(a)[0];
    }
    if a == 1 && method != ZetaMethod::EulerMaclaurin {
        im = s.imag().abs();
        re = s.real().abs();
        /*
        if (im < prec or method == 'borwein') and not derivative:
            try:
                if verbose:
                    print "zeta: Attempting to use the Borwein algorithm"
                return _zeta(s, **kwargs)
            except NotImplementedError:
                if verbose:
                    print "zeta: Could not use the Borwein algorithm"
                pass
        */
        if im > 500.0 * prec && 10.0 * re < prec && derivative <= 4 || method == ZetaMethod::RiemannSiegel {
            if verbose {
                println!("zeta: Attempting to use the Riemann-Siegel algorithm");
            }
            return rs_zeta(s, derivative);
            //ctx.prec = prec
        }
    }
    if s == 1 {
        return Complex::with_val(prec, (Special::Infinity, 0.0));
    }
    abss = s.abs();
    if abss.is_infinite() {
        if s.real().is_infinite() {
            if d == 0 {
                return Complex::with_val(prec, (1.0, 0.0));
            }
            return Complex::with_val(prec, (0.0, 0.0));
        }
        return s * 0.0;
    } else if abss.is_nan() {
        return 1.0 / s;
    }
    if s.real() > 2 * prec && a == 1 && derivative == 0 {
        return Complex::with_val(prec, (1.0, 0.0)) + mpc_pow(Complex::with_val(prec, (2.0, 0.0)), -s);
    }
    return _hurwitz(s, a, d);
}

fn siegelz(t: Complex, derivative: u32, prec: u32) -> Complex {
    d = derivative;
    //prec = self.prec;
    /*
    t_re = t.real();
    t_im = t.imag();
    let mut v;
    if t_re.abs() > 500 * prec and Pow::pow(t_im, 2) < t_re {
        v = rs_z(t, d);
        if t.imag().is_zero() {
            return Complex::with_val(prec, (v.real(), 0.0));
        }
        return v;
    }
    */
    let prec = t.prec() + 21;
    t.set_prec(prec);
    let e1 = mpc_expj(siegeltheta(t).into(), 0);
    let z = zeta(Float::with_val(prec, 0.5) + Complex::with_val(prec, (0, 1)) * t, ZetaMethod::None);
    if d == 0 {
        v = e1 * z;
        //self.prec = prec;
        v.set_prec(t.prec());
        if t.imag().is_zero() {
            return Complex::with_val(prec, (v.real(), 0.0));
        }
        return v;
    }
    let z1 = zeta(Float::with_val(prec, 0.5) + Complex::with_val(prec, (0, 1)) * t, 1);
    let theta1 = siegeltheta(t, 1);
    if d == 1 {
        v =  Complex::with_val(prec, (0.0, 1.0)) * e1 * (z1 + z * theta1);
        //self.prec = prec;
        v.set_prec(t.prec());
        if t.imag().is_zero() {
            return Complex::with_val(prec, (v.real(), 0.0));
        }
        return v;
    }
    let z2 = zeta(0.5 + Complex::with_val(prec, (0.0, 1.0)) * t, 2);
    theta2 = siegeltheta(t, 2);
    comb1 = theta1 * theta1 - Complex::with_val(prec, (0.0, 1.0)) * theta2;
    let terms;
    if d == 2 {
        terms = vec![2*z1*theta1, z2, z*comb1];
        v = sum_accurately(terms, 1, prec, false);
        v = -e1*v;
        //ctx.prec = prec;
        v.set_prec(t.prec());
        if t.imag().is_zero() {
            return Complex::with_val(prec, (v.real(), 0.0));
        }
        return v;
    }
    prec += 10;
    let z3 = zeta(0.5 + Complex::with_val(prec, (0.0, 1.0)) * t, 3);
    let theta3 = siegeltheta(t, 3);
    let comb2 = mpc_pow_int(theta1, 3) - Complex::with_val(prec, (0.0, 3.0)) * theta1 * theta2 - theta3;
    if d == 3 {
        terms = vec![3*theta1*z2, 3*z1*comb1, z3+z*comb2];
        v = sum_accurately(terms, 1, prec, false);
        v = Complex::with_val(prec, (0.0, -1.0)) * e1 * v;
        //self.prec = prec;
        v.set_prec(t.prec());
        if t.imag().is_zero() {
            return Complex::with_val(prec, (v.real(), 0.0));
        }
        return v;
    }
    let z4 = zeta(0.5 + Complex::with_val(prec, (0.0, 1.0)) * t, 4);
    let theta4 = siegeltheta(t, 4);
    terms = vec![mpc_pow_int(theta1, 4), Complex::with_val(prec, (0.0, -6.0)) * theta1 * theta1 * theta2, -3 * theta2 * theta2, -4 * theta1 * theta3, Complex::with_val(prec, (0.0, 1.0)) * theta4];
    let comb3 = sum_accurately(terms, 1);
    if d == 4 {
        terms = vec![6 * theta1 * theta1 * z2, Complex::with_val(prec, (0.0, -6.0)) * z2 * theta2, 4 * theta1 * z3, 4 * z1 * comb2, z4, z * comb3];
        v = sum_accurately(terms, 1, prec, false);
        v =  e1 * v;
        //self.prec = prec;
        v.set_prec(prec);
        if t.imag().is_zero() {
            return Complex::with_val(prec, (v.real(), 0.0));
        }
        return v;
    } else if d > 4 {
        let h = |x| siegelz(x, 4, prec);
        return diff(h, t, d-4);
    }
}

fn mag(x: &Float) -> i32 {
    return x.get_exp().unwrap() + (x.get_significand().unwrap().significant_bits() as i32);
}

fn sure_number_block(n: i64) -> usize {
    /*
    The number of good Rosser blocks needed to apply
    Turing method
    */
    if n < 9 * Pow::pow(10, 5) {
        return 2;
    }
    let lngp = grampoint(n - 100).ln();
    let brent = 0.0061 * Pow::pow(lngp, 2) + 0.08 * lngp;
    let trudgian = 0.0031 * Pow::pow(lngp, 2) + 0.11 * lngp;
    if brent < trudgian {
        return brent.ceil() as i64;
    } else {
        return trudgian.ceil() as i64;
    }
}

fn count_variations(V: Vec<Float>) -> i64 {
    let mut icount = 0;
    for n in 1..V.len() {
        if V[n - 1] * V[n] < 0 {
            icount += 1;
        }
    }
    return icount;
}


#[derive(PartialEq)]
enum FindRootMethod {
    Illinois,
    Pegasus,
    Anderson,
    Mdnewton
}


fn _getm(method: FindRootMethod) -> Box<dyn Fn(f64, f64) -> f64> {
    if method == FindRootMethod::Illinois {
        return Box::new(|_fz: f64, _fb: f64| {
            return 0.5;
        });
    } else if method == FindRootMethod::Pegasus {
        return Box::new(|fz: f64, fb: f64| {
            return fb/(fb + fz);
        });
    } else if method == FindRootMethod::Anderson {
        return Box::new(|fz: f64, fb: f64| {
            let m = 1.0 - fz/fb;
            if m > 0.0 {
                return m;
            } else {
                return 0.5;
            }
        });
    } else {
        return Box::new(|_fz: f64, _fb: f64| {
            return 0.5;
        });
    }
}

struct Illinois {
    step: i32,
    maxsteps: i32,
    converged: bool, 
    a: Complex,
    b: Complex,
    f: fn(Complex) -> Complex,
    fa: Complex,
    fb: Complex,
    tol: f64,
    verbose: bool,
    method: FindRootMethod,
    getm: fn(Float, Float) -> Float,
    queue: VecDeque<(Complex, Float)>,
}


impl Illinois {
    fn new(self, f: fn(Complex) -> Complex, x0: (Complex, Complex), tol: f64, method: FindRootMethod) -> Illinois {
        /*
        if x0.len() != 2 {
            panic!("expected interval of 2 points, got {}", x0.len());
        }
        */
        let mut i = Illinois {
            a: x0.0,
            b: x0.1,
            f: f,
            fa: Complex::with_val(53, (0.0, 0.0)),
            fb: Complex::with_val(53, (0.0, 0.0)),
            tol: tol,
            step: 0,
            maxsteps: 30,
            converged: false,
            verbose: false,
            method: method,
            getm: _getm(self.method),
            queue: VecDeque::with_capacity(30),
        };
        if self.verbose {
            println!("using {} method", self.method);
        }
        return i;
    }
    
    
}

impl Iterator for Illinois {
    type Item = (Complex, Complex);
    
    fn next(&mut self) -> Option<<Self as Iterator>::Item> {
        if self.queue.len() == 0 {
            if self.step < self.maxsteps && !self.converged {
                self.iter();
            } else {
                return None;
            }
        }
        return Some(self.queue.pop_front());
    }
    
    fn iter(&mut self) {
        if self.step == 0 {
            self.fa = (self.f)(self.a);
            self.fb = (self.f)(self.b);
        }
        for i in 0..10 {
            let l = self.b - self.a;
            if l == 0.0 {
                self.step += 1;
                self.converged = true;
                self.queue.push_back((Complex::with_val(l.prec(), (0.0, 0.0)), 0.0));
                break;
            }
            let s = (self.fb - self.fa) / l;
            let z = self.a - self.fa / s;
            let fz = self.f(z);
            if fz.abs() < self.tol {
                if self.verbose {
                    println!("canceled with z = {}", z);
                }
                self.step += 1;
                self.converged = true;
                self.queue.push_back((z, l));
                break;
            }
            let m;
            if fz * self.fb < 0 {
                self.a = self.b;
                self.fa = self.fb;
                self.b = z;
                self.fb = fz;
            } else {
                m = self.getm(fz, fb);
                self.b = z;
                self.fb = fz;
                self.fa = m * self.fa;
            }
            if self.verbose && m && self.method != FindRootMethod::Illinois {
                println!("m: {}", m);
            }
            self.step += 1;
            self.queue.push_back(((a + b)/2, l.abs()));
            if self.step >= self.maxsteps {
                break;
            }
        }
    }
}





/*
enum2solver = HashMap::(newton:Newton, 'secant':Secant, 'mnewton':MNewton,
              'halley':Halley, 'muller':Muller, 'bisect':Bisection,
              'illinois':Illinois, 'pegasus':Pegasus, 'anderson':Anderson,
              'ridder':Ridder, 'anewton':ANewton, 'mdnewton':MDNewton}
*/
//enum2solver = HashMap::from([(FindRootMethod::Illinois, Illinois), (FindRootMethod::Mdnewton, MDNewton)]);

// 
// https://github.com/mpmath/mpmath/blob/master/mpmath/calculus/optimization.py
// 
// f = lambda x: ctx.rs_z(x, 1);
// t = findroot(f, (t0, t1), findRootMethod.Illinois, false)
fn findroot(f: Fn(Complex) -> Complex, x0: (Complex, Complex), solver: FindRootMethod, tol: f64) -> Complex {
    verbose = false;
    verify = true;
    // solver = Secant;
    solver = FindRootMethod::Illinois;
    maxsteps = 0;
    //prec = ctx.prec
    prec += 20;
    tol = eps * Pow::pow(2, 10);
    /*
    if 'd1f' in kwargs {
        kwargs['df'] = kwargs['d1f']
    }
    */
    // x0 = [convert(x) for x in x0]
    
    let s = match solver {
            FindRootMethod::Illinois => Illinois::new(f, x0, tol, FindRootMethod::Illinois),
            FindRootMethod::Mdnewton => MDNewton::new(f, x0, tol),
            _ => panic!("None for enum FindRootMethod"),
        };
    
    /*
    if isinstance(f, (list, tuple)):
        f2 = copy(f)
        def tmp(*args):
            return [fn(*args) for fn in f2]
        f = tmp
    */
    
    /*
    // multidimensional functions
    try:
        fx = f(*x0)
        multidimensional = isinstance(fx, (Vec, tuple, Matrix))
    except TypeError:
        fx = f(x0[0])
        multidimensional = False
    if 'multidimensional' in kwargs:
        multidimensional = kwargs['multidimensional']
    if multidimensional:
        # only one multidimensional solver available at the moment
        solver = MDNewton
        if 'norm' not in kwargs:
            norm = lambda x: norm(x, 'inf')
            kwargs['norm'] = norm
        else:
            norm = kwargs['norm']
    else:
        norm = abs
    */
    multidimensional = false;
    norm = |x| { x.abs() };
    
    // happily return starting point if it's a root
    if norm(fx) == 0 {
        /*
        if multidimensional {
            return Matrix(x0);
        } else {
            return x0[0];
        }
        */
        return x0;
    }
    
    // f, x0, tol, method
    //let s = solver::new(f, x0, tol, FindRootMethod.Illinois);
    
    if maxsteps == 0 {
        maxsteps = s.maxsteps;
    }
    let mut x;
    let mut i = 0;
    for (x, err) in s.iter() {
        if verbose {
            println!("x:     {}", x);
            println!("error: {}", err);
        }
        i += 1;
        if err < tol * max(1, norm(x)) || i >= maxsteps {
            break;
        }
    }
    if i == 0 {
        panic!("Could not find root using the given solver. Try another starting point or tweak arguments.");
    }
    /*
    if not isinstance(x, (list, tuple, matrix)) {
        xl = [x];
    } else {
        xl = x;
    }
    */
    xl = x;
    if verify && Pow::pow(norm(f(*xl)), 2) > tol {
        //panic!("Could not find root within given tolerance. ({} > {}) Try another starting point or tweak arguments.", Pow::pow(norm(f(*xl)), 2), tol));
    }
    x.set_prec(prec);
    return x;
}


fn separate_zeros_in_block(zero_number_block: usize, mut T: Vec<Float>, mut V: Vec<Float>, limitloop: u32, fp_tolerance: f64) -> (Vec<Float>, Vec<Float>, bool) {
    let mut loopnumber = 0;
    let mut variations = count_variations(V);
    let prec = max(T[0].prec(), V[0].prec());
    while variations < zero_number_block && loopnumber < limitloop {
        let mut a = T[0];
        let mut v = V[0];
        let mut newT = vec![a];
        let mut newV = vec![v];
        variations = 0;
        for n in 1..T.len() {
            let b2 = T[n];
            let mut u = V[n];
            if u * v > 0 {
                let alpha = ((u as f64)/(v as f64)).sqrt();
                b = (alpha*a+b2) / (alpha+1);
            } else {
                b = (a+b2) / 2;
            }
            let mut w;
            if fp_tolerance < 10 {
                w = siegelz(b, 0, 53);
                if w.abs() < fp_tolerance {
                    w = siegelz(b, 0, b.prec());
                }
            } else {
                w = siegelz(b, 0, b.prec());
            }
            if v * w < 0 {
                variations += 1;
            }
            newT.push(b);
            newV.push(w);
            u = V[n];
            if u * w < 0 {
                variations += 1;
            }
            newT.push(b2);
            newV.push(u);
            a = b2;
            v = u;
        }
        T = newT;
        V = newV;
        loopnumber += 1;
        if limitloop > ITERATION_LIMIT && loopnumber > 2 && variations + 2 == zero_number_block {
            let mut dtMax = 0;
            let mut dtSec = 0;
            let mut kMax = 0;
            for k1 in 1..T.len() {
                let dt = T[k1] - T[k1 - 1];
                if dt > dtMax {
                    kMax = k1;
                    dtSec = dtMax;
                    dtMax = dt;
                } else if dt < dtMax && dt > dtSec {
                    dtSec = dt;
                }
            }
            if dtMax > 3 * dtSec {
                f = |x| rs_z(x, 1);
                let t0 = T[kMax - 1];
                let t1 = T[kMax];
                //let t = findroot(f, (t0, t1), FindRootMethod.Illinois, false);
                let t = findroot(f, (t0, t1), FindRootMethod.Illinois, 0.0);
                v = siegelz(t, 0, prec);
                if t0 < t && t < t1 && v * V[kMax] < 0 {
                    T.insert(kMax, t);
                    V.insert(kMax, v);
                }
            }
        }
        variations = count_variations(V);
    }
    if variations == zero_number_block {
        separated = true;
    } else {
        separated = false;
    }
    return (T, V, separated);
}

const ITERATION_LIMIT: u32 = 4;

fn search_supergood_block(&self, n: i64, fp_tolerance: f64) -> (i64, (i64, i64), Vec<>, Vec<>) {
    // To use for n > 400_000_000
    let sb = sure_number_block(n);
    let number_goodblocks = 0;
    let mut m2 = n - 1;
    let (mut t, mut v, mut b) = compute_triple_tvb(m2);
    let mut Tf = vec![t];
    let mut Vf = vec![v];
    while b < 0 {
        m2 += 1;
        (t, v, b) = compute_triple_tvb(m2);
        Tf.push(t);
        Vf.push(v);
    }
    let mut goodpoints = vec![m2];
    let mut T = vec![t];
    let mut V = vec![v];
    let mut A;
    let mut B;
    let mut separated = false;
    while number_goodblocks < 2*sb {
        m2 += 1;
        (t, v, b) = compute_triple_tvb(m2);
        T.push(t);
        V.push(v);
        while b < 0 {
            m2 += 1;
            (t, v, b) = compute_triple_tvb(m2);
            T.push(t);
            V.push(v);
        }
        goodpoints.push(m2);
        let zn = T.len() - 1;
        let (A, B, separated) = separate_zeros_in_block(zn, T, V, limitloop=ITERATION_LIMIT, fp_tolerance=fp_tolerance);
        let _ = Tf.pop();
        Tf.extend_from_slice(A);
        let _ = Vf.pop();
        Vf.extend_from_slice(B);
        if separated {
            number_goodblocks += 1;
        } else {
            number_goodblocks = 0;
        }
        T = vec![t];
        V = vec![v];
    }
    // Now the same procedure to the left
    number_goodblocks = 0;
    m2 = n-2;
    (t, v, b) = compute_triple_tvb(m2);
    Tf.insert(0, t);
    Vf.insert(0, v);
    while b < 0 {
        m2 -= 1;
        (t, v, b) = compute_triple_tvb(m2);
        Tf.insert(0, t);
        Vf.insert(0, v);
    }
    goodpoints.insert(0, m2);
    T = [t];
    V = [v];
    while number_goodblocks < 2*sb {
        m2 -= 1;
        (t, v, b) = compute_triple_tvb(m2);
        T.insert(0, t);
        V.insert(0, v);
        while b < 0 {
            m2 -= 1;
            (t, v, b) = compute_triple_tvb(m2);
            T.insert(0, t);
            V.insert(0, v);
        }
        goodpoints.insert(0, m2);
        let (mut A, mut B, separated) = separate_zeros_in_block(T.len() - 1, T, V, ITERATION_LIMIT, fp_tolerance);
        A.pop();
        Tf = A.extend_from_slice(Tf);
        B.pop();
        Vf = B.extend_from_slice(Vf);
        if separated {
            number_goodblocks += 1;
        } else {
            number_goodblocks = 0;
        }
        T = vec![t];
        V = vec![v];
    }
    let r = goodpoints[2*sb];
    let lg = goodpoints.len();
    let s = goodpoints[lg-2*sb-1];
    let (tr, vr, br) = compute_triple_tvb(r);
    let ar = Tf.iter().position(|x| x == tr);
    let (ts, vs, bs) = compute_triple_tvb(s);
    let as1 = Tf.iter().position(|x| x == ts);
    T = &Tf[ar..(as1+1)];
    V = &Vf[ar..(as1+1)];
    (A, B, separated) = separate_zeros_in_block(s - r, T, V, ITERATION_LIMIT, fp_tolerance);
    if separated {
        return (n - r - 1, (r, s), A, B);
    }
    let q = goodpoints[sb];
    let lg = goodpoints.len();
    let t = goodpoints[lg - sb - 1];
    let (tq, vq, bq) = compute_triple_tvb(q);
    let aq = Tf.iter().position(|x| x == tq);
    let (tt, vt, bt) = compute_triple_tvb(t);
    let at = Tf.iter().position(|x| x == tt);
    T = &Tf[aq..(at+1)];
    V = &Vf[aq..(at+1)];
    return (n - q - 1, (q, t), T, V);
}


// 
// https://github.com/mpmath/mpmath/blob/master/mpmath/functions/zetazeros.py#L190
// 
fn compute_triple_tvb(n: i64) -> (Float, Float, Float) {
    let t = grampoint(n);
    let mut v = siegelz(t, 0, 53);
    if mag(v.abs()) < mag(t) - 45 {
        v = siegelz(t, 0, t.prec());
    }
    let b;
    if n % 2 == 0 {
        b = v;
    } else {
        b = -v;
    }
    return (t, v, b);
}

fn find_rosser_block_zero(n: i64) -> (i64, (i64, i64), Vec<Float>, Vec<Float>) {
    // for n < 400_000_000 determines a block were one find our zero
    for k in 0..(_ROSSER_EXCEPTIONS.len()/2) {
        a = _ROSSER_EXCEPTIONS[2*k][0];
        b = _ROSSER_EXCEPTIONS[2*k][1];
        if (a <= n-2) && (n-1 <= b) {
            let t0 = grampoint(a);
            let t1 = grampoint(b);
            let v0 = siegelz(t0, 0, 53);
            let v1 = siegelz(t1, 0, 53);
            let my_zero_number = n - a - 1;
            let zero_number_block = b - a;
            let pattern = _ROSSER_EXCEPTIONS[2*k+1];
            return (my_zero_number, (a, b), vec![t0, t1], vec![v0, v1]);
        }
    }
    let mut k = n-2;
    let (mut t, mut v, mut b) = compute_triple_tvb(k);
    let T = vec![t];
    let V = vec![v];
    while b < 0 {
        k -= 1;
        (t, v, b) = compute_triple_tvb(k);
        T.insert(0, t);
        V.insert(0, v);
    }
    let my_zero_number = n - k - 1;
    let mut m = n-1;
    (t, v, b) = compute_triple_tvb(m);
    T.push(t);
    V.push(v);
    while b < 0 {
        m += 1;
        (t, v, b) = compute_triple_tvb(m);
        T.push(t);
        V.push(v);
    }
    return (my_zero_number, (k, m), T, V);
}


// 
// https://github.com/mpmath/mpmath/blob/master/mpmath/functions/zetazeros.py#L136
// 
fn separate_my_zero(my_zero_number: i64, zero_number_block, T: Vec<Float>, V: Vec<Float>, prec: u32) -> Float {
    let variations = 0;
    let v0 = V[0];
    let k0;
    let leftv;
    let rightv;
    for k in 1..V.len() {
        v1 = V[k];
        if v0 * v1 < 0 {
            variations += 1;
            if variations == my_zero_number {
                k0 = k;
                leftv = v0;
                rightv = v1;
            }
        }
        v0 = v1;
    }
    let t1 = T[k0];
    let t0 = T[k0-1];
    //ctx.prec = prec
    let wpz = wpzeros(my_zero_number * my_zero_number.ln());
    let guard = 4 * mag(my_zero_number);
    let precs = vec![prec + 4];
    index = 0;
    while precs[0] > 2*wpz {
        index += 1;
        precs.insert(0, precs[0] / 2 + 3 + 2 * index);
    }
    prec = precs[0] + guard;
    r = findroot(|x| siegelz(x), (t0, t1), FindRootMethod::Illinois);
    z = Complex::with_val(prec, (0.5, r));
    for p in 1..precs.len() {
        z.set_prec(precs[p] + guard);
        let znew = z - zeta(z) / zeta(z, 1);
        z = Complex::with_val(prec + guard, (0.5, znew.imag()));
    }
    return z.imag();
}


fn zetazero(n: i64) {
    info = false;
    /*
        >>> mp.dps = 15
        >>> zetazero(542964976,info=True)
        ((0.5 + 209039046.578535j), [542964969, 542964978], 6, '(013111110)')

    This means that the zero is between Gram points 542964969 and 542964978;
    it is the 6-th zero between them. Finally (01311110) is the pattern
    of zeros in this interval. The numbers indicate the number of zeros
    in each Gram interval (Rosser blocks between parenthesis). In this case
    there is only one Rosser block of length nine.
    */
    if n < 0 {
        return zetazero(-n).conjugate();
    } else if n == 0 {
        raise panic!("n must be nonzero.");
    }
    wpinitial = prec;
    let (wpz, fp_tolerance) = comp_fp_tolerance(n);
    let mut prec = wpz;
    let my_zero_number;
    let block;
    let mut T;
    let mut V;
    if n < 400_000_000 {
        (my_zero_number, block, T, V) = find_rosser_block_zero(n);
    } else {
        (my_zero_number, block, T, V) = search_supergood_block(n, fp_tolerance);
    }
    let zero_number_block = block.1 - block.0;
    let separated;
    (T, V, separated) = separate_zeros_in_block(zero_number_block, T, V, Special::Infinity, fp_tolerance);
    /*
    if info {
        pattern = pattern_construct(block, T, V);
    }
    */
    prec = max(wpinitial, wpz);
    let t = separate_my_zero(my_zero_number, zero_number_block, T, V, prec);
    let v = Complex::with_val(prec, (0.5, t));
    prec = wpinitial;
    /*
    if info {
        return (v,block,my_zero_number,pattern);
    } else {
        return v;
    }
    */
    return v;
}

fn giant_steps(start: i64, target: i64) -> Vec<i64> {
    let n = 2;
    let mut L = vec![target];
    while L.last().unwrap() > start * n {
        L.push(L.last().unwrap()/n + 2);
    }
    L.reverse();
    return L;
}


fn isqrt_fast(x: i64) {
    /*
    # 0 Newton iterations good to 52 bits
    # 1 Newton iterations good to 104 bits
    # 2 Newton iterations good to 208 bits
    # 3 Newton iterations good to 416 bits
    */
    if x < Float::with_val(800, 1.0) << 800 {
        y = x.isqrt() as i64;
        if x >= Float::with_val(100, 1.0) << 100 {
            y = (y + x/y) >> 1;
            if x >= Float::with_val(200, 1.0) << 200 {
                y = (y + x/y) >> 1;
                if x >= Float::with_val(400, 1.0) << 400 {
                    y = (y + x/y) >> 1;
                }
            }
        }
        return y;
    }
    let mut bc = x.bit_length();
    let guard_bits = 10;
    x <<= 2 * guard_bits;
    bc += 2 * guard_bits;
    bc += bc & 1;
    let hbc = bc / 2;
    let startprec = min(50, hbc);
    // Newton iteration for 1/sqrt(x), with floating-point starting value
    let mut r = (Pow::pow(2, 2 * startprec) / (x >> (bc - 2 * startprec)).sqrt()) as i64;
    let mut pp = startprec;
    for p in giant_steps(startprec, hbc) {
        // r**2, scaled from real size 2**(-bc) to 2**p
        let r2 = (r*r) >> (2*pp - p);
        // x*r**2, scaled from real size ~1.0 to 2**p
        let xr2 = ((x >> (bc-p)) * r2) >> p;
        // New value of r, scaled from real size 2**(-bc/2) to 2**p
        r = (r * ((3<<p) - xr2)) >> (pp+1);
        pp = p;
    }
    // (1/sqrt(x))*x = sqrt(x)
    return (r * (x>>hbc)) >> (p + guard_bits);
}

const EXP_SERIES_U_CUTOFF: u32 = 1500;

fn exponential_series(mut x: Float, utype: u32, prec: u32) -> (Float, Float) {
    let sign;
    if x < 0 {
        x = -x;
        sign = 1;
    } else {
        sign = 0;
    }
    let mut r = (0.5 * Pow::pow(prec, 0.5)) as i64;
    let xmag = x.bit_length() - prec;
    r = max(0, xmag + r);
    let extra = 10 + 2 * max(r, -xmag);
    let wp = prec + extra;
    x <<= extra - r;
    one = Float::with_val(wp, 1.0) << wp;
    alt = (utype == 2);
    if prec < EXP_SERIES_U_CUTOFF {
        let a = (x * x) >> wp;
        let x2 = a;
        let x4 = (x2 * x2) >> wp;
        let mut s0 = Float::with_val(wp, 0.0);
        let mut s1 = Float::with_val(wp, 0.0);
        let mut k = 2;
        while a != 0 {
            a /= (k - 1) * k;
            s0 += a; 
            k += 2;
            a /= (k - 1) * k;
            s1 += a;
            k += 2;
            a = (a * x4) >> wp;
        }
        s1 = (x2 * s1) >> wp;
        if alt {
            c = s1 - s0 + one;
        } else {
            c = s1 + s0 + one;
        }
    } else {
        let u = (0.3 * Pow::pow(prec as f64, 0.35)) as usize;
        let mut a = (x * x) >> wp;
        let x2 = a;
        let mut xpowers = vec![one, x2];
        for i in 1..u {
            xpowers.push((xpowers.last().unwrap() * x2) >> wp);
        }
        let mut sums = vec![Complex::with_val(prec,(0.0, 0.0)); u as usize];
        let mut k = 2;
        while a {
            for i in 0..u {
                a /= (k - 1) * kl;
                if alt && k & 2 != 0 {
                    sums[i] -= a;
                } else {
                    sums[i] += a;
                }
                k += 2;
            }
            a = (a * xpowers[-1]) >> wp
        }
        for i in 1..u {
            sums[i] = (sums[i] * xpowers[i]) >> wp;
        }
        c = sum(sums) + one;
    }
    /*
    if utype == 0 {
        s = isqrt_fast(c * c - (Float::with_val(wp, 1.0) << wp));
        if sign != 0 {
            v = c - s;
        } else {
            v = c + s;
        }
        for i in 0..r {
            v = (v * v) >> wp;
        }
        return v >> extra;
    }
    */
    if utype == 1 || utype == 2 {
        let pshift = wp - 1;
        for i in 0..r {
            c = ((c*c) >> pshift) - one;
        }
        // todo: check this line
        s = isqrt_fast((one << wp) - c*c).abs();
        if sign {
            s = -s;
        }
        return (c >> extra, s >> extra);
    }
}


const COS_SIN_CACHE_PREC: u32 = 400;
const COS_SIN_CACHE_STEP: u32 = 8;
lazy_static! {
    static ref cos_sin_cache: Mutex<HashMap<i64, (Float, Float)>> = Mutex::new(HashMap::new());
}

fn cos_sin_basecase(mut x: Float, prec: u32) -> (Float, Float) {
    if prec > COS_SIN_CACHE_PREC {
        return exponential_series(x, 2, prec);
    }
    let precs = prec - COS_SIN_CACHE_STEP;
    let t = x >> precs;
    let n = t.to_integer().unwrap().to_i64().unwrap();
    let mut cos_t;
    let mut sin_t;
    if !cos_sin_cache.contains_key(&n) {
        let w = t << (10+COS_SIN_CACHE_PREC-COS_SIN_CACHE_STEP);
        (cos_t, sin_t) = exponential_series(w, 2, 10 + COS_SIN_CACHE_PREC);
        cos_sin_cache.insert(n, (cos_t >> 10, sin_t >> 10));
    }
    (cos_t, sin_t) = cos_sin_cache[&n];
    let offset = COS_SIN_CACHE_PREC - prec;
    cos_t >>= offset;
    sin_t >>= offset;
    x -= t << precs;
    let mut cos = Float::with_val(prec, 1) << prec;
    let mut sin = x;
    let mut k = 2;
    let mut a = -((x*x).to_integer().unwrap() >> prec);
    while a {
        a /= k;
        cos += a; 
        k += 1; 
        a = (a*x).to_integer().unwrap() >> prec;
        a /= k; 
        sin += a; 
        k += 1; 
        a = -((a*x).to_integer().unwrap() >> prec);
    }
    return ((cos * cos_t - sin * sin_t) >> prec, (sin * cos_t + cos * sin_t) >> prec);
}



// 
// https://docs.rs/rug/latest/rug/struct.Float.html#method.from_raw
// 
fn from_man_exp(mantissa: Integer, exponent: i32, prec: u32) -> Float {
    /*
    const LIMBS: [limb_t; 2] = [mantissa, 1 << (limb_t::BITS - 1)];
    const LIMBS_PTR: *const [limb_t; 2] = &LIMBS;
    const MANTISSA_DIGITS: u32 = limb_t::BITS * 2;
    const MPFR: mpfr_t = mpfr_t {
        prec: MANTISSA_DIGITS as prec_t,
        sign: -1,
        exp: exponent,
        d: unsafe { NonNull::new_unchecked(LIMBS_PTR.cast_mut().cast()) },
    };
    static F: Float = unsafe { Float::from_raw(MPFR) };
    return F;
    */
    let mut f = Float::with_val(prec, mantissa);
    f = f << exponent;
    return f;
}


// 
// https://github.com/mpmath/mpmath/blob/master/mpmath/libmp/libmpf.py#L1017
// 
fn mpf_perturb(mut x: Float, eps_sign: u32, prec: u32, rnd: rug::float::Round) -> Float {
    if rnd == Round::Nearest {
        x.set_prec_round(prec, Round::Nearest);
        return x;
    }
    let sign = x.signum();
    let man = x.get_significand().unwrap();
    let exp = x.get_exp().unwrap();
    let bc = x.prec() as i32;
    // let eps = (eps_sign, MPZ_ONE, exp + bc - prec - 1, 1);
    // let eps = Float::with_val(prec, 1.0) * Pow::pow(Float::with_val(prec, 2.0), exp + bc - prec - 1);
    let mut eps = Float::with_val(prec, 1.0);
    let shift = exp + bc - prec as i32 - 1;
    if shift >= 0 {
        eps = eps << shift;
    } else {
        eps = eps >> (-shift);
    }
    // eps.set_prec(1);
    let away;
    if sign != 0 {
        away = match rnd {
            Round::Down => 1 ^ eps_sign,
            Round::Up => 1 ^ eps_sign,
            _ => 0 ^ eps_sign,
            };
    } else {
        away = match rnd {
            Round::Up => 1 ^ eps_sign,
            _ => 0 ^ eps_sign,
            };
    }
    if away != 0 {
        x += eps;
    }
    x.set_prec_round(prec, rnd);
    return x;
}


// 
// https://github.com/mpmath/mpmath/blob/master/mpmath/libmp/libelefun.py#L1259
// 
fn mod_pi2(man: Integer, exp: Integer, mag: i32, mut wp: u32) -> (Float, Integer, u32) {
    let offset;
    let mut t;
    let in;
    if mag > 0 {
        let mut i = 0;
        loop {
            let cancellation_prec = 20 << i;
            let wpmod = wp + mag + cancellation_prec;
            let pi2 = pi(wpmod - 1);
            let pi4 = pi2 >> 1;
            offset = wpmod + exp;
            if offset >= 0 {
                t = man << offset;
            } else {
                t = man >> (-offset);
            }
            let (fn, y) = t.div_rem(pi2);
            let small;
            if y > pi4 {
                small = pi2 - y;
            } else {
                small = y;
            }
            if small >> (wp + mag - 10) {
                in = fn.to_integer();
                t = y >> mag;
                wp = wpmod - mag;
                break;
            }
            i += 1;
        }
    } else {
        wp += -mag;
        offset = exp + wp;
        if offset >= 0 {
            t = man << offset;
        } else {
            t = man >> (-offset);
        }
        in = Integer::from(0);
    }
    return t, in, wp;
}


//
// https://github.com/mpmath/mpmath/blob/master/mpmath/libmp/libelefun.py#L1295
// 
fn mpf_cos_sin(x: Float, bpi: bool, prec: u32) -> (Float, Float) {
    let rnd = Round::Down;
    let which = 0;
    let sign = x.signum();
    let man = x.get_significand().unwrap();
    let exp = x.get_exp().unwrap();
    let bc = x.prec();
    let c;
    let s;
    if man.is_zero() {
        if exp == 0 {
            (c, s) = Float::with_val(prec, Special::Nan), Float::with_val(prec, Special::Nan);
        } else {
            (c, s) = Float::with_val(prec, 1.0), Float::with_val(prec, 0.0);
        }
        if which == 0 {
            return (c, s);
        } /* else if which == 1 {
            return c;
        } else if which == 2 { 
            return s;
        } else if which == 3 {
            return s;
        } */
    }
    let mag = bc as i32 + exp;
    let mut wp = prec as i32 + 10;
    if mag < 0 {
        if mag < -wp {
            if bpi {
                x = x * pi(wp);
            }
            c = mpf_perturb(Float::with_val(prec, 1.0), 1, prec, rnd);
            s = mpf_perturb(x, 1 - sign, prec, rnd);
            if which == 0 {
                return (c, s);
            } /* else if which == 1 {
                return c;
            } else if which == 2 { 
                return s;
            } else if which == 3 {
                return mpf_perturb(x, sign, prec);
            } */
        }
    }
    
    let t;
    let n;
    if bpi {
        if exp >= -1 {
            if exp == -1 {
                c = Float::with_val(wp, 0.0);
                s = match (man & 2).bitxor(sign) {
                        0 => Float::with_val(wp, 1.0);
                        1 => None
                    };
            } else if exp == 0 {
                (c, s) = (Float::with_val(wp, Special::Nan), Float::with_val(wp, 0.0));
            } else {
                (c, s) = (Float::with_val(wp, 1.0), Float::with_val(wp, 0.0));
            }
            if which == 0 { 
                return (c, s);
            }
            /*
            if which == 1 {
                return c;
            }
            if which == 2 {
                return s;
            }
            if which == 3 {
                return mpf_div(s, c, prec, rnd);
            }
            */
        }
        n = ((man >> (-exp-2)) + 1) >> 1;
        man = man - (n << (-exp-1));
        mag2 = man.significant_bits() + exp;
        wp = prec + 10 - mag2;
        offset = exp + wp;
        if offset >= 0 {
            t = Float::with_val(wp, man << offset);
        } else {
            t = Float::with_val(wp, man >> (-offset));
        }
        t = (t * pi(wp)) >> wp;
    } else {
        (t, n, wp) = mod_pi2(man, exp, mag, wp);
    }
    
    (t, n, wp) = mod_pi2(man, exp, mag, wp);
    (c, s) = cos_sin_basecase(t, wp);
    let m = n & 3;
    if m == 1 {
        (c, s) = -s, c;
    } else if m == 2 {
        (c, s) = -c, -s;
    } else if m == 3 {
        (c, s) = s, -c;
    }
    if sign != 0 {
        s = -s;
    }
    if which == 0 {
        c = from_man_exp(c, -(wp as i32), prec);
        s = from_man_exp(s, -(wp as i32), prec);
        return (c, s);
    } /* else if which == 1 {
        return from_man_exp(c, -(wp as i32), prec);
    } else if which == 2 {
        return from_man_exp(s, -(wp as i32), prec);
    } else if which == 3 {
        return from_rational(s, c, prec);
    } */
}

fn mpf_expj(z: Float, prec: u32) -> Float {
    // todo: check this line
    return mpf_cos_sin(z, prec);
}

// 
// https://github.com/mpmath/mpmath/blob/master/mpmath/libmp/libmpc.py#L810
// 
fn mpc_expj(z: Complex, prec: u32) -> Complex {
    let mut re = z.real();
    let mut im = z.imag();
    if im.is_zero() {
        re = mpf_cos_sin(re.clone(), false, prec);
        im = &Float::with_val(prec, 0.0);
    } else if re.is_zero() {
        im.signum_mut() = -im.signum();
        re = im.exp();
        im = &Float::with_val(prec, 0.0);
    } else {
        im.signum_mut() = -im.signum();
        im.set_prec(prec + 10);
        ey = im.exp();
        let (c, s) = mpf_cos_sin(re.clone(), false, prec + 10);
        re = ey * c;
        im = ey * s;
        //re.set_prec(prec);
        //im.set_prec(prec);
    }
    return Complex::with_val(prec, (re, im));
}

// 
// https://github.com/mpmath/mpmath/blob/master/mpmath/functions/rszeta.py#L766
// 
fn Rzeta_set(s: Complex, derivatives: Vec<u32>) -> HashMap<u32, Complex> {
    derivatives = vec![0];
    let der = derivatives.iter().max().unwrap();
    let wpinitial = s.prec();
    let mut t = s.imag();
    let sigma = s.real();
    let mut prec = 15;
    t.set_prec(15);
    a = (t / (2.0 * pi(15))).sqrt();
    sigma.set_prec(15);
    let asigma = a.pow(sigma);
    let A1 = Integer::from(2).pow(mag(asigma) - 1);
    let eps = Pow::pow(2, -(wpinitial as i32));
    let eps1 = eps/6.0;
    let eps2 = eps * A1/3.0;
    //prec = 15;
    let b;
    let c;
    let A;
    let B1;
    if *sigma > 0 {
        b = 2.0;
        c = Float::with_val(15, 9).pow(sigma) / 4.44288;
        A = Float::with_val(15, 9).pow(sigma);
        B1 = 1.0;
    } else {
        b = 2.25158;
        c = Float::with_val(15, 2).pow(-sigma) / 4.44288;
        A = Float::with_val(15, 2).pow(-sigma);
        B1 = 1.10789;
    }
    //prec = 15;
    let L = Float::with_val(15, 1.0);
    while 3 * c * (L * 0.5).gamma() * Float::with_val(15, b * a).pow(-L) >= eps2 {
        L = L + 1;
    }
    if L.partial_cmp(2) == Some(Ordering::Less) {
        L = 2;
    }
    if (3*L) >= 2*a*a/25.0 || 3*L+2+sigma < 0 || sigma.abs() > a/2.0 {
        //prec = wpinitial
        panic!("NotImplementedError, Riemann-Siegel can not compute with such precision.");
    }
    let eps3 = eps2/(4*L);
    let eps4 = eps3/(3*L);
    let M = aux_M_Fp(A, eps4, a, B1, L);
    let mut Fp = HashMap::new();
    for n in M..(3*L-2) {
        Fp.insert(n, 0);
    }
    let h1 = eps4/(632*A);
    let mut h2 = pi(15) * pi(15) * B1 * a * Float::with_val(15, 3.0).sqrt() * e(15) * e(15);
    h2 = h1 * Pow::pow(h2 / Pow::pow(M, 2), (M as f64 - 1.0) / 3.0) / M;
    let h3 = min(h1,h2);
    let mut J = 12;
    let mut jvalue = Pow::pow(2 * pi(15), J) / Float::with_val(15, J + 1).gamma();
    while jvalue > h3 {
        J += 1;
        jvalue = (2 * pi(15)) * jvalue / J;
    }    
    let mut eps5 = HashMap::with_capacity(22);
    let foreps5 = pi(15) * pi(15) * B1 * a;
    for m in 0..22 {
        let aux1 = foreps5.pow(m as f32 / 3.0) / (Float::with_val(15, 316.0) * A);
        // Unstable feature https://github.com/rust-lang/rust/issues/99842
        let mut aux2 = Float::with_val(53, m+1).gamma() / ((m as f32)/3.0 + 0.5).gamma();
        aux2 = aux2.sqrt();
        eps5.insert(m, aux1 * aux2 * eps4);
    }
    let twenty = min(3 * L - 3, 21) + 1;
    let aux = 6812 * J;
    let mut wpfp = mag(Float::with_val(53, 44*J));
    for m in 0..twenty {
        wpfp = max(wpfp, mag(aux * Float::with_val(53, m+1).gamma()/eps5[m]));
    }
    let prec = (wpfp + mag(t) + 20) as u32;
    let a = (t/(2 * pi(prec))).sqrt();
    let N = a.floor();
    let mut p = 1 - 2 * (a - N);
    let num = (p * Float::with_val(prec, 2.0).pow(ImmutablePower::new(wpfp))).floor();
    let difference = p * Float::with_val(prec, 2.0).pow(ImmutablePower::new(wpfp)) - num;
    if difference >= 0.5 {
        num += 1;
    }
    p = num * Float::with_val(prec, 2).pow(ImmutablePower::new(-(wpfp as i32)));
    let eps6 = Pow::pow(2 * pi(prec), J) / (Float::with_val(prec, J + 1.0).gamma() * 3.0 * J);
    let mut cc = HashMap::new();
    let mut cont = HashMap::new();
    (cont, pipowers) = coef(J, eps6);
    cc = cont.copy();
    Fp = HashMap::with_capacity(3 * L - 2);
    for n in M..(3*L-2) {
        Fp.insert(n, 0);
    }
    prec = wpfp;
    for m in 0..(M+1) {
        let mut sumP = 0;
        for k in (2*J-m-1)..-1.stepby(-1) {
            sumP = (sumP * p) + cc[&k];
        }
        Fp.insert(m, sump);
        for k in 0..(2*J-m-1) {
            cc[&k] = (k + 1) * cc[k + 1];
        }
    }
    let mut wpd = HashMap::with_capacity(L);
    let d1 = max(6, mag(Float::with_val(53, 40*L*L)));
    let d2 = 13 + mag((1+sigma.abs())*A) - mag(eps4) - 1;
    let const = (8.0 / (pi(prec) * pi(prec) * a * a * B1 * B1)).ln() / 2;
    for n in 0..L {
        let d3 = mag(Float::with_val(53, n - 0.5).gamma().sqrt()) - (n * const).floor() + d2;
        wpd.insert(n, max(d3, d1));
    }
    prec = wpd[1] + 10;
    let psigma = 1 - (2 * sigma);
    let mut d = HashMap::new();
    d.insert((0, 0, -2), 0);
    d.insert((0, 0, -1), 0);
    d.insert((0, 0, 0), 1);
    d.insert((0, 0, 1), 0);
    d.insert((0, -1, -2), 0);
    d.insert((0, -1, -1), 0);
    d.insert((0, -1, 0), 1);
    d.insert((0, -1, 1), 0);
    for n in 1..L {
        prec = wpd[&n] + 10;
        for k in 0..(3*n/2+1) {
            let m = 3*n-2*k;
            if m != 0 {
                let m1 = Float::with_val(prec, 1.0) / m;
                let c1 = m1 / 4.0;
                let c2 = (psigma*m1) / 2;
                let c3 = -(m+1);
                d[(0, n, k)] = c3 * d[(0, n-1, k-2)] + c1 * d[(0, n-1, k)] + c2 * d[(0, n-1, k-1)];
            } else {
                d[(0, n, k)] = 0;
                for r in 0..k {
                    let add = d[(0, n, r)] * (Float::with_val(prec, 1.0) * Float::factorial(2*k - 2*r).complete() / Float::factorial(k-r).complete());
                    d[(0, n, k)] -= Pow::pow(-1, k-r) * add;
                }
            }
        }
        d[(0, n, -2)] = 0;
        d[(0, n, -1)] = 0;
        d[(0, n, 3*n/2+1)] = 0;
    }
    for mu in -2..(der+1) {
        for n in -2..L {
            for k in -3..max(1, 3*n/2+2) {
                if mu < 0 || n < 0 || k < 0 || k > 3*n/2 {
                    d[(mu, n, k)] = 0;
                }
            }
        }
    }
    for mu in 1..(der+1) {
        for n in 0..L {
            //prec = wpd[&n] + 10;
            sigma.set_prec(wpd[&n] + 10);
            for k in 0..(3*n/2+1) {
                d[(mu-2, n-2, k-3)].set_prec(sigma.prec());
                d[(mu-1, n-2, k-3)].set_prec(sigma.prec());
                d[(mu-1, n-1, k-1)].set_prec(sigma.prec());
                let aux = (2 * mu - 2) * d[(mu-2, n-2, k-3)] + 2 * (sigma+n-2) * d[(mu-1, n-2, k-3)];
                d[(mu, n, k)] = aux - d[(mu-1, n-1, k-1)];
            }
        }
    }
    let mut wptcoef = HashMap::with_capacity(L);
    let mut wpterm = HashMap::with_capacity(L);
    //prec = 15;
    let c1 = mag(Float:with_val(15, 40*(L+2)));
    let c2 = mag(Float:with_val(15, 68*(L+2)*A));
    let c4 = mag(B1 * a * pi(15).sqrt()) - 1;
    for k in 0..L {
        let c3 = c2 - k * c4 + mag(Float::with_val(15, Float::factorial(k + 0.5))) / 2.0;
        wptcoef.insert(k, max(c1, c3 - mag(eps4) + 1) + 1 + 10);
        wpterm.insert(k, max(c1, mag(Float:with_val(15, L + 2.0)) + c3 - mag(eps3) + 1) + 1 + 10);
    }
    let mut fortcoef = HashMap::new();
    for mu in derivatives {
        for k in 0..L {
            for ell in -2..(3*k/2+1) {
                fortcoef.insert((mu, k, ell), Complex::with_val(prec, (0.0, 0.0)));
            }
        }
    }
    for mu in derivatives {
        for k in 0..L {
            prec = wptcoef[&k];
            for ell in 0..(3*k/2+1) {
                fortcoef[(mu, k, ell)] = d[(mu, k, ell)] * Fp[3*k-2*ell] / pipowers[2*k-ell];
                fortcoef[(mu, k, ell)] = fortcoef[(mu, k, ell)] / Pow::pow(2 * Complex::with_val(prec, (0.0, 1.0)), ell);
            }
        }
    }
    let mut trunc_a = move |t: Float| {
        t.set_prec(wp + 2);
        let aa = (t / (2 * pi(wp + 2))).sqrt();
        aa.set_prec(prec);
        aa
    };
    tcoef = HashMap::new();
    for chi in derivatives {
        for k in 0..L {
            for ell in -2..(3*k/2+1) {
                tcoef.insert((chi, k, ell), Complex::with_val(prec, (0.0, 0.0)));
            }
        } 
    }
    prec = wptcoef[0] + 3;
    t.set_prec(wptcoef[0] + 3);
    aa = trunc_a(t);
    la = -aa.ln();
    for chi in derivatives {
        for k in 0..L {
            //prec = wptcoef[&k];
            for ell in 0..(3*k/2+1) {
                tcoef[(chi, k, ell)] = Float::with_val(wptcoef[&k], 0.0);
                for mu in 0..(chi+1) {
                    fortcoef[(chi-mu, k, ell)].set_prec(wptcoef[&k]);
                    let tcoefter = mpf_binomial(Float::with_val(wptcoef[&k], chi), Float::with_val(wptcoef[&k], mu)) * Pow::pow(la, mu) * fortcoef[(chi-mu, k, ell)];
                    tcoef[(chi, k, ell)] += tcoefter;
                }
            }
        }
    }
    //prec = wptcoef[0] + 2;
    let mut av = HashMap::with_capacity(L);
    a.set_prec(wptcoef[0] + 2);
    av.insert(0, Float::with_val(wptcoef[0] + 2, 1.0));
    av.insert(1, av[0]/a);
    //prec = wptcoef[0];
    av[1].set_prec(wptcoef[0]);
    for k in 2..L {
        av[k] = av[k-1] * av[1];
    }
    tv = HashMap::new();
    for chi in derivatives {
        for k in 0..L {
            //prec = wptcoef[&k];
            for ell in 0..(3 * k/2 + 1) {
                tcoef[(chi, k, ell)].set_prec(wptcoef[&k]);
                av[&k].set_prec(wptcoef[&k]);
                tv[(chi, k, ell)] = tcoef[(chi, k, ell)] * av[&k];
            }
        }
    }
    term = HashMap::new();
    for chi in derivatives {
        for n in 0..L {
            //prec = wpterm[&n];
            te = Float::with_val(wpterm[&n], 0.0);
            for k in 0..(3*n/2+1) {
                tv[(chi, n, k)].set_prec(wpterm[&n]);
                te += tv[(chi, n, k)];
            }
            term[(chi, n)] = te;
        }
    }
    rssum = HashMap::new();
    prec = 15;
    rsbound = pi(15).sqrt() * c / (b * a);
    wprssum = mag(Float:with_val(15, 4.4) * Pow::pow(L+3, 2) * rsbound / eps2);
    wprssum = max(wprssum, mag(Float:with_val(15, 10 * (L+1))));
    prec = wprssum;
    for chi in derivatives {
        rssum[chi] = Float::with_val(wprssum, 0.0);
        for k in 1..(L+1) {
            term[(chi, L-k)].set_prec(wprssum);
            rssum[chi] += term[(chi, L-k)];
        }
    }
    prec = 15;
    let A2 = Pow::pow(2, mag(rssum[0]));
    let eps8 = eps/(3.0 * A2);
    let T = t * (t / (2.0 * pi(15))).ln();
    let wps3 = 5 + mag((1.0 + (2.0 / eps8) * Pow::pow(a, -sigma)) * T);
    prec = wps3;
    t.set_prec(wps3);
    let tpi = t / (2.0 * pi(wps3));
    let arg = (t / 2.0) * tpi.ln() - (t / 2.0) - pi(wps3) / 8.0;
    let U = mpc_expj(-arg);
    let a = trunc_a(t);
    let asigma = Pow::pow(a, -sigma);
    let S3 = Pow::pow(-1, N-1) * asigma * U;
    prec = 15;
    let wpsum = 4 + mag((N + Pow::pow(N, 1 - sigma)) * N.ln() / eps1);
    prec = wpsum + 10;
    /*
    # This can be improved
    S1 = HashMap::new();
    for chi in derivatives {
        S1.insert(chi, Float::with_val(prec, 0.0));
    }
    for n in 1..(N.to_integer().unwrap() + 1):
        let ln = n.ln();
        let expn = (-ln * (sigma + Complex::with_val(prec, (0.0, 1.0)) * t)).exp();
        for chi in derivatives {
            let term = Pow::pow(-ln, chi) * expn;
            S1[&chi] += term;
        }
    }
    */
    s.set_prec(wpsum + 10);
    //let S1 = _zetasum(s, 1, int(N)-1, derivatives)[0];
    let S1 = mpc_zetasum(s, 1, N.to_integer() - 1, derivatives)[0];
    prec = 15;
    S1[der].set_prec(15);
    let absS1 = S1[der].abs();
    rssum[der].set_prec(15);
    S3.set_prec(15);
    let absS2 = (rssum[der] * S3).abs();
    let wpend = max(6, wpinitial + mag(6.0 * (3.0 * absS1 + 7.0 * absS2)));
    //prec = wpend;
    S3.set_prec(wpend);
    let mut rz = HashMap::new();
    for chi in derivatives {
        S1[&chi].set_prec(wpend);
        rssum[&chi].set_prec(wpend);
        rz[&chi] = S1[&chi] + rssum[&chi] * S3;
        rz[&chi].set_prec(wpinitial);
    }
    //prec = wpinitial;
    return rz;
}

// 
// https://github.com/mpmath/mpmath/blob/master/mpmath/libmp/gammazeta.py#L764
// 
fn mpc_psi(m: u32, mut z: Complex, prec: u32) {
    // 
    // polygamma function
    // 
    if m == 0 {
        return z.gamma();
    }
    let re = z.real();
    let im = z.imag();
    let wp = prec + 20;
    let sign = re.signum();
    let man = re.get_significand().unwrap();
    let exp = re.get_exp().unwrap();
    let bc = re.prec();
    if im.get_significand().unwrap() == 0 {
        if im.is_infinite() || im.is_nan() {
            return (Special::Nan, Special::Nan);
        }
    }
    if man.is_zero() {
        if re.is_infinite() && im.is_zero() {
            return (0.0, 0.0);
        }
        if re.is_nan() {
            return (Special::Nan, Special::Nan);
        }
    }
    let w = re.to_integer();
    let n = (0.4*wp + 4*m).floor() as i64;
    let mut s = Complex::with_val(wp, (0.0, 0.0));
    z.set_prec(wp);
    if w < n {
        for k in w..n {
            s = s + Pow::pow(z, -m-1);
            z = z + Float::with_val(wp, 1.0);
        }
    }
    let zm = Pow::pow(z, -m);
    let z2 = Pow::pow(z, -2);
    // 1/m*(z+N)^m
    integral_term = zm / Float::with_val(wp, m);
    s = s + integral_term;
    // 1/2*(z+N)^(-(m+1))
    s = s + (zm / z) * Float::with_val(wp, 0.05);
    let mut a = Float::with_val(wp, m + 1.0);
    let mut b = Float::with_val(wp, 2.0);
    let mut k = 1;
    // Important: we want to sum up to the *relative* error,
    // not the absolute error, because psi^(m)(z) might be tiny
    s.set_prec(10);
    let mut magn = s.abs();
    magn = magn.get_exp().unwrap() + magn.prec();
    let eps = Float::with_val(wp, 1) >> magn - (wp as i32) + 2;
    s.set_prec(wp);
    loop {
        zm = zm * z2;
        let bern = mpf_bernoulli(2*k, wp);
        let mut term = zm * bern * a / b;
        s = s + term;
        term.set_prec(10);
        szterm = term.abs_round(Round::Down);
        //szterm.set_prec(10);
        if k > 2 && szterm <= eps {
            break;
        }
        a *= (m + 2 * k) * (m + 2 * k + 1);
        b *= (2 * k + 1) * (2 * k + 2);
        k += 1;
    }
    // Scale and sign factor
    v = s * (m+1).gamma_round(Round::Down);
    if !(m & 1) {
        *v.mut_imag() *= -1;
        *v.mut_real() *= -1;
    }
    return v;
}

// 
// https://github.com/mpmath/mpmath/blob/master/mpmath/functions/rszeta.py#L1178
// 
fn zeta_half(s: Complex, k: i32) -> Complex {
    let wpinitial = s.prec();
    let sigma = s.real();
    let t = s.imag();
    prec = 53;
    let X;
    let M1;
    if sigma > 0 {
        X = s.abs().sqrt();
        M1 = 2.0 * (t / (2.0 * pi(prec))).sqrt();
    } else {
        X = Pow::pow(2.0 * pi(prec), sigma - 1) * Pow::pow((1.0 - s).abs(), 0.5 - sigma);
        M1 = 4.0 * t * X;
    }
    let abst = (0.5 - s).abs();
    let T = 2.0 * abst * abst.log();
    let mut wpbasic = max(6, 3 + mag(t));
    let wpbasic2 = 2 + mag(2.12 * M1 + 21.2 * M1 * X + 1.3 * M1 * X * T) + wpinitial + 1;
    wpbasic = max(wpbasic, wpbasic2);
    let wptheta = max(4, 3 + mag(2.7 * M1 * X) + wpinitial + 1);
    let wpR = 3 + mag(1.1 + 2.0 * X) + wpinitial + 1;
    t.set_prec(wptheta);
    sigma.set_prec(wptheta);
    let theta = siegeltheta(t - Complex::with_val(wptheta, (0, 1)) * (sigma - Float::with_val(wptheta, 0.5)));
    let ps1;
    if k > 0 { 
        //ps1 = mpc_psi(0, s / 2.0).real() / 2.0 - pi(wptheta).ln() / 2.0;
        ps1 = (s / 2.0).gamma().real() / 2.0 - pi(wptheta).ln() / 2.0;
    }
    if k > 1 { 
        ps2 = -mpc_psi(1, s / 2.0).imag() / 4.0;
    }
    if k > 2 { 
        ps3 = -mpc_psi(2, s / 2.0).real() / 8.0;
    }
    if k > 3 { 
        ps4 = mpc_psi(3, s / 2.0).imag() / 16.0;
    }
    s.set_prec(wpR);
    let xrz = Rzeta_set(s, 0..(k+1));
    let yrz = HashMap::with_capacity(k+1);
    for chi in 0..(k+1) {
        yrz[chi] = xrz[chi].conjugate();
    }
    theta.set_prec(wpbasic);
    let exptheta = mpc_expj(-2.0 * theta);
    let zv;
    if k == 0 {
        zv = xrz[0] + exptheta * yrz[0];
    } else if k == 1 {
        let zv1 = -yrz[1] - 2 * yrz[0] * ps1;
        zv = xrz[1] + exptheta * zv1;
    } else if k == 2 {
        let zv1 = 4 * yrz[1] * ps1 + 4 * yrz[0] * Pow::pow(ps1, 2) + yrz[2] + Complex::with_val(wpbasic, (0.0, 2.0)) * yrz[0] * ps2;
        zv = xrz[2] + exptheta * zv1;
    } else if k == 3 {
        let mut zv1 = -12 * yrz[1] * Pow::pow(ps1, 2) - 8 * yrz[0] * Pow::pow(ps1, 3) - 6 * yrz[2] * ps1 - Complex::with_val(wpbasic, (0.0, 6.0)) * yrz[1] * ps2;
        zv1 = zv1 - Complex::with_val(wpbasic, (0.0, 12.0)) * yrz[0] * ps1 * ps2 - yrz[3] + 2 * yrz[0] * ps3;
        zv = xrz[3] + exptheta * zv1;
    } else if k == 4 {
        let mut zv1 = 32 * yrz[1] * Pow::pow(ps1, 3) + 16 * yrz[0] * Pow::pow(ps1, 4) + 24 * yrz[2] * Pow::pow(ps1, 2);
        zv1 = zv1 + Complex::with_val(wpbasic, (0.0, 48.0)) * yrz[1] * ps1 * ps2 + Complex::with_val(wpbasic, (0.0, 48.0)) * yrz[0] * Pow::pow(ps1, 2) * ps2;
        zv1 = zv1 + Complex::with_val(wpbasic, (0.0, 12.0)) * yrz[2] * ps2 - 12 * yrz[0] * Pow::pow(ps2, 2) + 8 * yrz[3] * ps1 - 8 * yrz[1] * ps3;
        zv1 = zv1 - 16 * yrz[0] * ps1 * ps3 + yrz[4] - Complex::with_val(wpbasic, (0.0, 2.0)) * yrz[0] * ps4;
        zv = xrz[4] + exptheta * zv1;
    }
    zv.set_prec(wpinitial);
    return zv;
}

fn rs_zeta(s, k) {
    return zeta_half(s, k);
}

fn aux_M_Fp(xA: f64, xeps4: i64, a: f64, xB1: f64, xL: i64) -> i64 {
    // COMPUTING M  NUMBER OF DERIVATIVES Fp[m] TO COMPUTE
    let mut aux1 = 126.0657606 * xA / xeps4;
    aux1 = aux1.ln();
    let aux2 = (2*math_pi.ln() + xB1.ln() + a.ln()) / 3 - 2*math_pi.ln() / 2;
    let mut m = 3 * xL - 3;
    let mut aux3 = ((m+1).ln_gamma() - (m/3.0 + 2).ln_gamma())/2.0 - (m+1).ln_gamma()/2.0;
    while aux1 < m*aux2 + aux3 && m > 1 {
        m = m - 1;
        aux3 = ((m+1).ln_gamma() - (m/3.0+2).ln_gamma())/2 - ((m+1)/2.0).ln_gamma();
    }
    return m;
}

fn aux_J_needed(xA: f64, xeps4: f64, a: f64, xB1: f64, xM: f64) -> i64 {
    // DETERMINATION OF J THE NUMBER OF TERMS NEEDED IN THE TAYLOR SERIES OF F.
    let h1 = xeps4 / (632.0 * xA);
    let mut h2 = xB1 * a * 126.31337419529260248;
    h2 = h1 * Pow::pow(h2 / Pow::pow(xM, 2), (xM - 1) / 3) / xM;
    return min(h1, h2) as i64;
}

// 
// https://github.com/mpmath/mpmath/blob/master/mpmath/libmp/libintmath.py#L444
// 
fn eulernum(m: i64) -> Float {
    if m & 1 {
        return Float::with_val(prec, 0.0);
    }
    let mut n = m;
    let mut a = Vec::new();
    for i in [0, 0, 1, 0, 0, 0] {
        a.push(Float::with_val(prec, 0.0));
    }
    let mut suma = Float::with_val(prec, 1.0);
    for n in 1..(m+1) {
        for j in (n+1)..-1.step_by(-2) {
            a[j+1] = (j-1)*a[j] + (j+1)*a[j+2];
        }
        a.push(0);
        let mut suma = 0;
        for k in (n+1)..-1.step_by(-2) {
            suma += a[k+1];
        }
    }
    return Pow::pow(-1, n/2) * suma / Pow::pow(2, n);
}


// 
// https://github.com/mpmath/mpmath/blob/master/mpmath/libmp/gammazeta.py#L253
// 
fn euler_fixed(mut prec: u32) -> Float {
    prec += 30;
    let p = ((prec as f32)/4.0 * (2 as f32).ln()).ln2() as i32 + 1;
    let n = Integer::from(2).pow(p);
    let npow2 = n.pow(2);
    let A = Float::with_val(prec, -p as f32 * (prec as f32).ln2());
    let U = A.clone();
    let B = Float::with_val(prec, 1.0) << prec;
    let V = B.clone();
    let k = Integer::from(1);
    loop {
        B = (B * npow2 / k.pow(2)).floor();
        A = ((A * npow2  / k + B) / k).floor();
        U += A;
        V += B;
        if A.abs() < 100 && B.abs() < 100 {
            break;
        }
        k += 1;
    }
    return (U << (prec - 30)) / V;
}


// 
// https://github.com/mpmath/mpmath/blob/master/mpmath/libmp/libmpc.py#L825
// 
fn mpc_expjpi(z: Complex, prec: u32) -> Complex {
    let mut re = z.real();
    let mut im = z.imag();
    if im.is_zero() {
        return Complex::with_val(prec, mpf_cos_sin_pi(re, prec));
    }
    sign = im.signum();
    man = im.get_significand().unwrap();
    exp = im.get_exp();
    bc = im.prec();
    let mut wp = prec + 10;
    if man {
        wp += max(0, exp + bc);
    }
    im = -pi(wp) * im;
    im.set_prec(wp);
    if re.is_zero() {
        im.set_prec(prec);
        return Complex::with_val(prec, (im.exp(), 0.0));
    }
    im.set_prec(prec + 10);
    let ey = im.exp();
    let z = Complex::with_val(prec + 10, mpf_cos_sin_pi(re, prec + 10));
    *z.mut_real() = ey * z.real();
    *z.mut_imag() = ey * z.imag();
    z.set_prec(prec);
    return z;
}

fn _coef(J: i32, eps: i32) -> RsCache {
    let newJ = J + 2;
    let neweps6 = eps / 2.0;
    let wpvw = max(mag(Float::with_val(53, 10 * (newJ + 3))), 4 * newJ + 5 - mag(Float:with_val(53, neweps6)));
    let E = eulernum(2 * newJ);
    let wppi = max(mag(Float:with_val(53, 40 * newJ)), mag(Float:with_val(53, newJ)) + 3 + wpvw);
    let mut prec = wppi;
    let mut pipower = HashMap::with_capacity(2 * newJ + 1);
    pipower.insert(0, Float::with_val(prec, 1.0));
    pipower.insert(1, pi(prec));
    for n in 2..(2*newJ+1) {
        pipower.insert(n, pipower[n-1] * pi(prec));
    }
    prec = wpvw + 2;
    let mut v = HashMap::with_capacity(newJ + 1);
    let mut w = HashMap::with_capacity(2 * newJ + 1);
    for n in 0..(newJ+1) {
        let mut va = Float::with_val(prec, Pow::pow(-1, n) * eulernum(2*n));
        va = va / Float::factorial(2.0*n).complete();
        v.insert(n, va * pipower[2*n]);
    }
    for n in 0..(2*newJ+1) {
        let mut wa = Float::with_val(prec, 1.0) / Float::factorial(n);
        wa = wa / Pow::pow(2, n);
        w.insert(n, wa * pipower[&n]);
    }
    prec = 15
    let wpp1a = 9 - mag(Float:with_val(53, neweps6));
    let mut P1 = HashMap::with_capacity(newJ + 1);
    let mut sump;
    for n in 0..(newJ+1) {
        //prec = 15;
        let wpp1 = max(mag(Float:with_val(53, 10 * (n + 4))), 4 * n + wpp1a);
        //prec = wpp1;
        sump = Complex::with_val(wpp1, (0.0, 0.0));
        for k in 0..(n+1) {
            sump += Pow::pow(-1, k) * v[k] * w[2*n-2*k];
        }
        sump.set_prec(wpp1);
        P1.insert(n, Pow::pow(-1, n+1) * Complex::with_val(wpp1, (0.0, 1.0)) * sump);
    }
    let mut P2 = HashMap::with_capacity(newJ+1);
    for n in 0..(newJ+1) {
        //prec = 15;
        let wpp2 = max(mag(Float:with_val(53, 10 * (n + 4))), 4 * n + wpp1a);
        //prec = wpp2;
        sump = Complex::with_val(wpp2, (0.0, 0.0));
        for k in 0..(n+1) {
            sump += Pow::pow(Complex::with_val(wpp2, (0.0, 1.0)), n-k) * v[k] * w[n-k];
        }
        sump.set_prec(wpp2);
        P2.insert(n, sump);
    }
    prec = 15;
    let wpc0 = 5 - mag(Float:with_val(15, neweps6));
    let mut wpc = max(6, 4 * newJ + wpc0);
    //prec = wpc;
    let mu = Float::with_val(wpc, 2.0).sqrt()/2.0;
    let nu = mpc_expjpi(Complex::with_val(wpc, (3.0/8.0, 0.0)))/2.0;
    let mut c = HashMap::with_capacity(2*newJ);
    for n in 0..newJ {
        //prec = 15;
        wpc = max(6, 4 * n + wpc0);
        c.insert(2*n, mu * P1[&n] + nu * P2[&n]);
        c[2*n].set_prec(wpc);
    }
    for n in 1..(2*newJ).step_by(2) {
        c.insert(n, 0);
    }
    rsc = RsCache::new(newJ, neweps6);
    rsc.cont = c;
    rsc.pipowers = pipower;
    return rsc;
}

struct RsCache {
    J: i32,
    eps: i32,
    cont: HashMap<i64, Complex>,
    pipowers: HashMap<i64, Float>
}

impl RsCache {
    fn new(j: i32, e: i32) -> RsCache {
        RsCache {
            J: j,
            eps: e,
            cont: HashMap::<i64, Complex>::new(),
            pipowers: HashMap::<i64, Float>::new()
        }
    }
}


lazy_static! {
    static ref _rs_cache: Mutex<RsCache> = Mutex::new(RsCache::new(0, 0));
}

fn coef(J: i32, eps: i32) {
    if J <= _rs_cache.J and eps >= _rs_cache.eps {
        return (_rs_cache.cont, _rs_cache.pipowers);
    }
    orig = _mp.prec;
    rsc = _coef(_mp, J, eps);
    _mp.prec = orig;
    /*
    if ctx is not ctx._mp {
        tpl[2] = dict((k,ctx.convert(v)) for (k,v) in tpl[2].items())
        tpl[3] = dict((k,ctx.convert(v)) for (k,v) in tpl[3].items())
    }
    */
    _rs_cache = rsc;
    return (_rs_cache.cont, _rs_cache.pipowers);
}


// 
// https://github.com/mpmath/mpmath/blob/master/mpmath/ctx_mp.py
// 
fn mpf_isnpint(x: Float) -> bool {
    // Determine if *x* is a nonpositive integer.
    if !x.is_infinite() {
        return x.signum() < 0 && x.get_exp() >= 0;
    } else {
        return false;
    }
}

// 
// https://github.com/mpmath/mpmath/blob/master/mpmath/ctx_mp.py
// 
fn mpc_isnpint(x: Complex) -> bool {
    return x.imag().is_zero() && mpf_isnpint(x.real());
}


// 
// https://github.com/mpmath/mpmath/blob/master/mpmath/functions/factorials.py
// 
fn gammaprod(a: Vec<Float>, b: Vec<Float>, eps: f64) -> Float {
    let _infsign = false;
    poles_num = Vec::new();
    poles_den = Vec::new();
    regular_num = Vec::new();
    regular_den = Vec::new();
    /*
    for x in a {
        [regular_num, poles_num][mpf_isnpint(x)].append(x)
    }
    for x in b { 
        [regular_den, poles_den][mpf_isnpint(x)].append(x)
    }
    */
    let prec = 0;
    for aa in a {
        prec = max(prec, aa.prec());
        if mpf_isnpint(aa) {
            poles_num.append(aa);
        } else {
            regular_num.append(aa);
        }
    }
    for bb in b {
        prec = max(prec, bb.prec());
        if mpf_isnpint(bb) {
            poles_den.append(bb);
        } else {
            regular_den.append(bb);
        }
    }
    if poles_num.len() < poles_den.len() {
        return Float::with_val(prec, 0.0);
    }
    if poles_num.len() > poles_den.len() {
        if _infsign {
            a = [x && x*(1 + eps) || x + eps for x in poles_num]
            b = [x && x*(1 + eps) || x + eps for x in poles_den]
            return sign(gammaprod(a + regular_num, b + regular_den)) * inf
        } else {
            return Float::with_val(prec, Special::Infinity);
        }
    }
    let mut p = Float::with_val(prec, 1.0);
    let orig = prec;
    prec = orig + 15;
    while poles_num.len() > 0 {
        let i = poles_num.pop();
        i.set_prec(prec);
        let j = poles_den.pop();
        j.set_prec(prec);
        p *= Pow::pow(-1, i+j) * (1-j).gamma() / (1-i).gamma();
    }
    for x in regular_num {
        p *= x.gamma();
    }
    for x in regular_den {
        p /= x.gamma();
    }
    //prec = orig;
    p.set_prec(orig);
    return p;
}


// 
// https://github.com/mpmath/mpmath/blob/master/mpmath/functions/factorials.py
// 
fn mpf_binomial(n: Float, k: Float) -> Float {
    let prec = max(n.prec(), k.prec());
    n1 = n + 1;
    n1.set_prec(2 * prec);
    k1 = k + 1;
    k1.set_prec(2 * prec);
    nk1 = n1 - k;
    //nk1.set_prec(2 * prec);
    return gammaprod(vec![n1], vec![k1, nk1], 1 >> min(32, prec/2));
}


fn Rzeta_simul(s, der=0) {
    let wpinitial = s.prec();
    t = s.imag();
    let xsigma = s.real();
    let ysigma = 1 - xsigma;
    let mut a = (t/(2 * pi(wpinitial))).sqrt();
    a.set_prec(15);
    let xasigma = Pow::pow(a, xsigma);
    let yasigma = Pow::pow(a, ysigma);
    let xA1 = Pow::pow(2, mag(xasigma)-1);
    let yA1 = Pow::pow(2, mag(yasigma)-1);
    let eps = Pow::pow(2, -(wpinitial as i32));
    let eps1 = eps / 6.0;
    let xeps2 = eps * xA1 / 3.0;
    let yeps2 = eps * yA1 / 3.0;
    let xb;
    let xc;
    let xA;
    let xB1;
    xsigma.set_prec(15);
    if xsigma > 0 {
        xb = Float::with_val(xsigma.prec(), 2.0);
        xc = Pow::pow(9, xsigma) / 4.44288;
        xA = Pow::pow(9, xsigma);
        xB1 = 1.0;
    } else {
        xb = 2.25158;
        xc = Pow::pow(2, -xsigma) / 4.44288;
        xA = Pow::pow(2, -xsigma);
        xB1 = 1.10789;
    }
    let yb;
    let yc;
    let yA;
    let yB1;
    ysigma.set_prec(xsigma.prec());
    if ysigma > 0 {
        yb = Float::with_val(ysigma.prec(), 2.0);
        yc = Pow::pow(9, ysigma) /  4.44288;
        yA = Pow::pow(9, ysigma);
        yB1 = 1.0;
    } else {
        yb = 2.25158;
        yc = Pow::pow(2, -ysigma) / 4.44288;
        yA = Pow::pow(2, -ysigma);
        yB1 = 1.10789;
    }
    let mut xL = Float::with_val(15, 1.0);
    while 3 * xc * (xL * 0.5).gamma() * Pow::pow(xb * a, -xL) >= xeps2 {
        xL = xL + 1;
    }
    xL = max(2, xL);
    let mut yL = Float::with_val(15, 1.0);
    while 3 * yc * (yL * 0.5).gamma() * Pow::pow(yb * a, -yL) >= yeps2 {
        yL = yL + 1;
    }
    yL = max(2, yL);
    if 3.0*xL >= 2.0*a*a/25.0 || 3.0*xL+2.0+xsigma < 0 || xsigma.abs() > a/2.0 || 3.0*yL >= 2.0*a*a/25.0 || 3.0*yL+2.0+ysigma < 0 || ysigma.abs() > a/2.0 {
        //ctx.prec = wpinitial;
        panic!("Riemann-Siegel can not compute with such precision");
    }
    let L = max(xL, yL);
    let xeps3 = xeps2 / (4.0*xL);
    let yeps3 = yeps2 / (4.0*yL);
    let xeps4 = xeps3 / (3.0*xL);
    let yeps4 = yeps3 / (3.0*yL);
    xM = aux_M_Fp(xA, xeps4, a, xB1, xL.to_integer());
    yM = aux_M_Fp(yA, yeps4, a, yB1, yL.to_integer());
    M = max(xM, yM);
    let mut h3 = aux_J_needed(xA, xeps4, a, xB1, xM);
    let h4 = aux_J_needed(yA, yeps4, a, yB1, yM);
    h3 = min(h3, h4);
    let mut J = 12;
    let mut jvalue = Pow::pow(2.0*pi(xsigma.prec()), J) / (J + 1).gamma();
    while jvalue > h3 {
        J = J + 1;
        jvalue = (2.0 * pi(xsigma.prec())) * jvalue / J;
    }
    let mut eps5 = HashMap::new();
    let xforeps5 = math_pi * math_pi * xB1 * a;
    let yforeps5 = math_pi * math_pi * yB1 * a;
    for m in 0..22 {
        let xaux1 = Pow::pow(xforeps5, m/3.0)/(316.0 * xA);
        let yaux1 = Pow::pow(yforeps5, m/3.0)/(316.0 * yA);
        let aux1 = min(xaux1, yaux1);
        let aux2 = Float::with_val(xsigma.prec(), m+1).gamma() / Float::with_val(xsigma.prec(), m/3.0+0.5).gamma();
        let aux2 = aux2.sqrt();
        eps5.insert(m, aux1 * aux2 * min(xeps4, yeps4));
    }
    let twenty = min(3*L-3, 21) + 1;
    let aux = 6812*J;
    let mut wpfp = mag(Float:with_val(53, 44*J));
    for m in 0..twenty {
        wpfp = max(wpfp, mag(aux * Float:with_val(53, m+1).gamma() / eps5[m]));
    }
    prec = wpfp + mag(t)+20;
    a = (t/(2.0 * pi(prec))).sqrt();
    N = a.floor();
    p = 1.0 - 2.0 * (a - N);
    num = (p * Pow::pow(2.0, wpfp)).floor();
    difference = p * Pow::pow(2.0, wpfp) - num;
    if difference >= 0.5 {
        num = num + 1;
    }
    p = Float::with_val(prec, num * Pow::pow(2.0, -(wpfp as i32)));
    eps6 = Pow::pow(2.0 * pi(prec), J)/(Float::with_val(prec, J+1).gamma()*3.0*J);
    let mut cc = HashMap::new();
    let mut cont = HashMap::new();
    let rsc = coef(J, eps6);
    cc = rsc.cont.clone();
    let mut Fp = HashMap::new();
    for n in M..(3*L-2) {
        Fp.insert(n, 0);
    }
    let mut Fp = HashMap::new();
    prec = wpfp;
    for m in 0..(M+1) {
        sumP = 0
        for k in (2*J-m-1)..-1.step_by(-1) {
            sumP = (sumP * p) + cc[k];
        }
        Fp.insert(m, sump);
        for k in 0..(2*J-m-1) {
            cc[k] = (k+1) * cc[k+1];
        }
    }
    let mut xwpd = HashMap::new();
    d1 = max(6, mag(Float:with_val(53, 40*L*L)));
    xd2 = 13 + mag((1+abs(xsigma))*xA) - mag(xeps4)-1
    xconst = (8.0/(pi(prec) * pi(prec) * a * a * xB1 * xB1)).ln() / 2.0;
    for n in 0..L {
        xd3 = mag(Float:with_val(53, n-0.5).gamma().sqrt()) - (n*xconst).floor() + xd2;
        xwpd[n] = max(xd3, d1);
    }
    prec = xwpd[1]  +10;
    xpsigma = 1-(2*xsigma);
    let mut xd = HashMap::new();
    xd.insert((0, 0, -2), 0); 
    xd.insert((0, 0, -1), 0); 
    xd.insert((0, 0, 0), 1); 
    xd.insert((0, 0, 1), 0);
    xd.insert((0, -1, -2), 0);
    xd.insert((0, -1, -1), 0); 
    xd.insert((0, -1, 0), 1); 
    xd.insert((0, -1, 1), 0);
    for n in 1..L {
        prec = xwpd[n] + 10;
        for k in 0..(3*n/2+1) {
            m = 3*n - 2*k;
            if m != 0 {
                let m1 = Float::with_val(prec, 1.0)/m;
                let c1 = m1/4;
                let c2 = (xpsigma*m1)/2;
                let c3 = -(m+1);
                xd[(0, n, k)] = c3 * xd[(0, n-1, k-2)] + c1 * xd[(0, n-1, k)] + c2 * xd[(0, n-1, k-1)];
            } else {
                xd[(0, n, k)] = Float::with_val(prec, 0.0);
                for r in 0..k {
                    add = xd[(0, n, r)] * Float::with_val(prec, 1.0) * Float::factorial(2*k-2*r).complete() / Float::factorial(k-r).complete();
                    xd[(0, n, k)] -= Pow::pow(-1, k-r) * add;
                }
            }
        }
        xd[(0, n, -2)] = 0; 
        xd[(0, n, -1)] = 0; 
        xd[(0, n, 3*n/2+1)] = 0;
    }
    for mu in -2..(der+1) {
        for n in -2..L {
            for k in -3..max(1, 3*n/2+2) {
                if mu<0 || n<0 || k<0 || k>3*n/2 {
                    xd.insert((mu, n, k), Float::with_val(prec, 0.0));
                }
            }
        }
    }
    for mu in 1..(der+1) {
        for n in 0..L {
            prec = xwpd[n] + 10;
            for k in 0..(3*n/2+1) {
                aux = (2*mu-2) * xd[(mu-2, n-2, k-3)] + 2 * (xsigma+n-2) * xd[(mu-1, n-2, k-3)];
                xd[(mu, n, k)] = aux - xd[(mu-1, n-1, k-1)];
            }
        }
    }
    ywpd = HashMap::with_capacity(L);
    d1 = max(6, mag(Float:with_val(53, 40*L*L)));
    yd2 = 13 + mag((1+abs(ysigma))*yA) - mag(yeps4) - 1;
    yconst = (8.0/(pi(prec) * pi(prec) * a * a * yB1 * yB1)).ln() / 2.0;
    for n in 0..L {
        yd3 = mag(Float:with_val(53, n-0.5).gamma().sqrt()) - (n*yconst).floor() + yd2;
        ywpd.insert(n, max(yd3, d1));
    }
    prec = ywpd[1] + 10;
    ysigma.set_prec(prec);
    ypsigma = 1 - (2*ysigma);
    yd = HashMap::new();
    yd.insert((0, 0, -2), 0);
    yd.insert((0, 0, -1), 0); 
    yd.insert((0, 0, 0), 1); 
    yd.insert((0, 0, 1), 0);
    yd.insert((0, -1, -2), 0); 
    yd.insert((0, -1, -1), 0); 
    yd.insert((0, -1, 0), 1); 
    yd.insert((0, -1, 1), 0);
    for n in 1..L {
        prec = ywpd[n]+10;
        for k in 0..(3*n/2+1) {
            m = 3*n-2*k;
            if m != 0 {
                m1 = Float::with_val(prec, 1.0) / m;
                c1 = m1 / 4.0;
                c2 = (ypsigma*m1) / 2.0;
                c3 = -(m+1);
                yd[(0, n, k)] = c3 * yd[(0, n-1, k-2)] + c1 * yd[(0, n-1, k)] + c2 * yd[(0, n-1, k-1)];
            } else {
                yd[(0, n, k)]=0
                for r in 0..k {
                    add = yd[(0, n, r)]*(Float::with_val(prec, 1.0) * Float::factorial(2*k-2*r).complete() / Float::factorial(k-r).complete());
                    yd[(0, n, k)] -= Pow::pow(-1, k-r)*add;
                }
            }
        }
        yd[(0, n, -2)] = 0; 
        yd[(0, n, -1)] = 0; 
        yd[(0, n, 3*n/2+1)] = 0;
    }
    for mu in -2..(der+1) {
        for n in -2..L {
            for k in -3..max(1, 3*n/2+2) {
                if mu<0 || n<0 || k<0 || k>3*n/2 {
                    yd[(mu, n, k)] = 0;
                }
            }
        }
    }
    for mu in 1..(der+1) {
        for n in 0..L {
            prec = ywpd[n] + 10;
            ysigma.set_prec(prec);
            for k in 0..(3*n/2+1) {
                yd[(mu-2, n-2, k-3)].set_prec(prec);
                yd[(mu-1, n-2, k-3)].set_prec(prec);
                aux = (2*mu-2) * yd[(mu-2, n-2, k-3)] + 2*(ysigma+n-2) * yd[(mu-1, n-2, k-3)];
                yd[(mu, n, k)] = aux - yd[(mu-1, n-1, k-1)];
            }
        }
    }
    let mut xwptcoef = HashMap::with_capacity(L);
    let mut xwpterm = HashMap::with_capacity(L);
    prec = 15
    let c1 = mag(Float:with_val(53, 40 * (L + 2)));
    let xc2 = mag(68 * (L+2) * xA);
    let xc4 = mag(xB1 * a * pi(prec).sqrt()) - 1;
    for k in 0..L {
        let xc3 = xc2 - k * xc4 + mag(Float:with_val(15, Float::factorial(k + 0.5))) / 2.0;
        xwptcoef.insert(k, (max(c1, xc3 - mag(xeps4) + 1) + 1 + 20) * 1.5);
        xwpterm.insert(k, max(c1, mag(Float:with_val(15, L+2)) + xc3 - mag(xeps3) + 1) + 1 + 20);
    }
    let mut ywptcoef = HashMap::new();
    let mut ywpterm = HashMap::new();
    prec = 15
    c1 = mag(Float:with_val(prec, 40*(L+2)));
    let yc2 = mag(68*(L+2)*yA);
    let yc4 = mag(yB1 * a * pi(prec).sqrt())-1;
    for k in 0..L {
        let yc3 = yc2 - k * yc4 + mag(Float:with_val(prec, Float::factorial(k + 0.5)))/2.0;
        ywptcoef.insert(k, ((max(c1,yc3-mag(yeps4)+1))+10)*1.5);
        ywpterm.insert(k, (max(c1,mag(L+2)+yc3-mag(yeps3)+1)+1)+10);
    }
    let mut xfortcoef = HashMap::new();
    for mu in 0..(der+1) {
        for k in 0..L {
            for ell in -2..(3*k/2+1) {
                xfortcoef.insert((mu, k, ell), 0);
            }
        }
    }
    for mu in 0..(der+1) {
        for k in 0..L {
            //ctx.prec = xwptcoef[k]
            for ell in 0..(3*k/2+1) {
                xfortcoef[(mu, k, ell)] = xd[(mu, k, ell)] * Fp[3*k-2*ell] / pipowers[2*k-ell];
                xfortcoef[(mu, k, ell)] = xfortcoef[(mu, k, ell)] / Pow::pow(Complex::with_val(xwptcoef[k], (0.0, 2.0)), ell);
            }
        }
    }
    let mut trunc_a = move |t| {
        t.set_prec(t.prec() + 2);
        aa = (t/(2*pi(t.prec()))).sqrt();
        aa.set_prec(t.prec() - 2);
        return aa;
    }
    xtcoef = HashMap::new();
    for mu in 0..(der+1) {
        for k in 0..L {
            for ell in -2..(3*k/2+1) {
                xtcoef.insert((mu, k, ell), 0);
            }
        }
    }
    prec = max(xwptcoef[0], ywptcoef[0])+3;
    t.set_prec(prec);
    aa = trunc_a(t);
    la = -aa.ln();
    for chi in 0..(der+1) {
        for k in 0..L {
            //prec = xwptcoef[&k];
            for ell in 0..(3*k/2+1) {
                xtcoef[(chi, k, ell)] = 0;
                for mu in 0..(chi+1) {
                    tcoefter = mpf_binomial(Float::with_val(xwptcoef[&k], chi), Float::with_val(xwptcoef[&k], mu)) * Pow::pow(la, mu) * xfortcoef[(chi-mu, k, ell)];
                    xtcoef[(chi, k, ell)] += tcoefter;
                }
            }
        }
    }
    let mut yfortcoef = HashMap::new();
    for mu in 0..(der+1) {
        for k in 0..L {
            //prec = ywptcoef[&k];
            for ell in -2..(3*k/2+1) {
                yfortcoef.insert((mu, k, ell), Complex::with_val(ywptcoef[&k], (0.0, 0.0)));
            }
        }
    }
    for mu in 0..(der+1) {
        for k in 0..L {
            //prec = ywptcoef[&k];
            for ell in 0..(3*k/2+1) {
                Fp[3 * k - 2 * ell].set_prec(ywptcoef[&k]);
                pipowers[2 * k - ell].set_prec(ywptcoef[&k]);
                yfortcoef[(mu, k, ell)] = yd[(mu, k, ell)] * Fp[3 * k - 2 * ell] / pipowers[2 * k - ell];
                yfortcoef[(mu, k, ell)] = yfortcoef[(mu, k, ell)] / Pow::pow(Complex::with_val(ywptcoef[&k], (0.0, 2.0)), ell);
            }
        }
    }
    let mut ytcoef = HashMap::new();
    for chi in 0..(der+1) {
        for k in 0..L {
            //prec = ywptcoef[&k];
            for ell in -2..(3*k/2+1) {
                ytcoef.insert((chi, k, ell), Complex::with_val(ywptcoef[&k], (0.0, 0.0)));
            }
        }
    }
    for chi in 0..(der+1) {
        for k in 0..L {
            //prec = ywptcoef[&k];
            for ell in 0..(3*k/2+1) {
                ytcoef[(chi, k, ell)] = 0;
                for mu in 0..(chi + 1) {
                    tcoefter = mpf_binomial(Float::with_val(ywptcoef[&k], chi), Float::with_val(ywptcoef[&k], mu)) * Pow::pow(la, mu) * yfortcoef[(chi-mu, k, ell)];
                    ytcoef[(chi, k, ell)] += tcoefter;
                }
            }
        }
    }
    prec = max(xwptcoef[0], ywptcoef[0])+2;
    let mut av = HashMap::with_capacity(L);
    av.insert(0, 1);
    av.insert(1, av[0]/a);
    prec = max(xwptcoef[0], ywptcoef[0]);
    for k in 2..L {
        av.insert(k, av[k-1] * av[1]);
        av[&k].set_prec(prec);
    }
    let mut xtv = HashMap::new();
    for chi in 0..(der+1) {
        for k in 0..L {
            //ctx.prec = xwptcoef[k];
            for ell in 0..(3*k/2+1) {
                xtv.insert((chi, k, ell), xtcoef[(chi, k, ell)] * av[k]);
                xtv[(chi, k, ell)].set_prec(xwptcoef[k]);
            }
        }
    }
    let mut ytv = HashMap::new();
    for chi in 0..(der+1) {
        for k in 0..L {
            //ctx.prec = ywptcoef[k];
            for ell in 0..(3*k/2+1) {
                ytv.insert((chi, k, ell), ytcoef[(chi, k, ell)] * av[k]);
                ytv[(chi, k, ell)].set_prec(ywptcoef[k]);
            }
        }
    }
    let mut xterm = HashMap::new();
    for chi in 0..(der+1) {
        for n in 0..L {
            //ctx.prec = xwpterm[n];
            te = Float::with_val(xwpterm[n], 0.0);
            for k in 0..(3*n/2+1) {
                te += xtv[chi,n,k];
            }
            xterm[chi,n] = te;
        }
    }
    let mut yterm = HashMap::new();
    for chi in 0..(der+1) {
        for n in 0..L {
            //ctx.prec = ywpterm[n];
            let mut te = Float::with_val(ywpterm[n], 0.0);
            for k in 0..(3*n/2+1) {
                te += ytv[(chi, n, k)];
            }
            yterm.insert((chi, n), te);
        }
    }
    let mut xrssum = HashMap::new();
    //prec = 15;
    xrsbound = pi(15).sqrt() * xc /(xb*a);
    xrsbound.set_prec(15);
    //prec = 15;
    xwprssum = mag(4.4 * Pow::pow(L+3, 2) * xrsbound / xeps2);
    xwprssum.set_prec(15);
    xwprssum = max(xwprssum, mag(Float:with_val(53, 10*(L+1))));
    //prec = xwprssum
    for chi in 0..(der+1) {
        xrssum.insert(chi, Float::with_val(xwprssum, 0.0));
        for k in 1..(L+1) {
            xterm[(chi, L-k)].set_prec(xwprssum);
            xrssum[chi] += xterm[(chi, L-k)];
        }
    }
    let mut yrssum = HashMap::with_capacity(der+1);
    //prec = 15;
    let mut yrsbound = pi(15).sqrt() * yc /(yb*a);
    yrsbound.set_prec(15);
    //prec = 15;
    let mut ywprssum = mag(4.4 * Pow::pow(L+3, 2) * yrsbound / yeps2)
    ywprssum.set_prec(15);
    ywprssum = max(ywprssum, mag(Float:with_val(15, 10*(L+1))));
    //prec = ywprssum;
    for chi in 0..(der+1) {
        yrs9sum.insert(chi, Float::with_val(ywprssum, 0.0));
        for k in 1..(L+1) {
            yrssum[chi] += yterm[chi, L-k];
        }
    }
    let A2 = Pow::pow(2, max(mag(xrssum[0].abs()), mag(yrssum[0].abs())));
    A2.set_prec(15);
    let eps8 = eps/(3*A2);
    eps8.set_prec(15);
    // todo: check this line
    T = t * (t / (2.0 * pi(15))).ln();
    T.set_prec(15);
    xwps3 = 5 +  mag((1.0 + (2.0 / eps8) * Pow::pow(a, -xsigma)) * T);
    ywps3 = 5 +  mag((1.0 + (2.0 / eps8) * Pow::pow(a, -ysigma)) * T);
    prec = max(xwps3, ywps3);
    tpi = t / (2.0 * pi(15));
    arg = (t / 2.0) * tpi.ln() - (t/2) - pi(15) / 8.0;
    U = mpc_expj(-arg);
    a = trunc_a(t);
    let xasigma = Pow::pow(a, -xsigma);
    let yasigma = Pow::pow(a, -ysigma);
    let xS3 = Pow::pow(-1, N-1) * xasigma * U;
    let yS3 = Pow::pow(-1, N-1) * yasigma * U;
    xwpsum = 4 + mag((N + Pow::pow(N, 1-xsigma)) * N.ln() /eps1);
    xwpsum.set_prec(15);
    ywpsum = 4 + mag((N + Pow::pow(N, 1-ysigma)) * N.ln() /eps1);
    ywpsum.set_prec(15);
    wpsum = max(xwpsum, ywpsum);
    prec = wpsum +10;
    /*
    # This can be improved
    let mut xS1 = HashMap::new();
    let mut yS1 = HashMap::new();
    for chi in 0..(der+1) {
        xS1.insert(chi, 0);
        yS1.insert(chi, 0);
    }
    for n in 1..(int(N)+1) {
        let ln = n.ln();
        let xexpn = (-ln * (xsigma + Complex::with_val(prec, (0.0, 1.0)) * t)).exp();
        let yexpn = (1/(n*xexpn)).conjugate();
        for chi in 0..(der+1) {
            pown = Pow::pow(-ln, chi);
            xS1[chi] += pown*xexpn;
            yS1[chi] += pown*yexpn;
        }
    }
    */
    let (xS1, yS1) = _zetasum(s, 1, int(N)-1, 0..(der+1), true);
    xabsS1 = xS1[der].abs();
    xabsS1.set_prec(15);
    xabsS2 = (xrssum[der] * xS3).abs();
    xabsS2.set_prec(15);
    xwpend = max(6, wpinitial + mag(6 * (3 * xabsS1 + 7 * xabsS2) ) )
    let mut xrz = HashMap::with_capacity(der+1);
    for chi in 0..(der+1) {
        xS1[chi].set_prec(xwpend);
        xrssum[chi].set_prec(xwpend);
        xrz[chi] = xS1[chi] + xrssum[chi] * xS3;
        xrz[chi].set_prec(wpinitial);
    }
    prec = 15;
    let yabsS1 = yS1[der].abs();
    let yabsS2 = (yrssum[der] * yS3).abs();
    let ywpend = max(6, wpinitial + mag(6 * (3 * yabsS1 + 7 * yabsS2)));
    prec = ywpend;
    let mut yrz = HashMap::new();
    for chi in 0..(der+1) {
        yrz.insert(chi, (yS1[chi] + yrssum[chi] * yS3).conjugate());
        yrz[chi].set_prec(wpinitial);
    }
    return (xrz, yrz);
}


fn z_offline(w: Complex, k: i32) {
    let mut prec = max(w.real().prec(), w.imag().prec());
    let s = Complex::with_val(prec, (0.5, 0.0)) + Complex::with_val(prec, (0.0, 1.0)) * w;
    let s1 = s;
    let s2 = (1 - s1).conjugate();
    let wpinitial = prec;
    prec = 35;
    let M1;
    let X;
    if s1.real() >= 0 {
        M1 = 2 * (s1.imag() / (2.0 * pi(prec))).sqrt();
        X = s1.abs().sqrt();
    } else {
        X = Pow::pow(2 * pi(prec), s1.real() - 1) * Pow::pow((1 - s1).abs(), 0.5 - s1.real());
        M1 = 4 * s1.imag() * X;
    }
    let M2;
    if s2.real() >= 0 {
        M2 = 2 * (s2.imag()/(2.0 * pi(prec))).sqrt();
    } else {
        M2 = 4 * s2.imag() * Pow::pow(2.0 * pi(prec), s2.real() - 1) * Pow::pow((1 - s2).abs(), 0.5 - s2.real());
    }
    let T = 2 * siegeltheta(w).abs();
    let aux1 = X.sqrt();
    let aux2 = aux1 * (M1 + M2);
    let aux3 = 3 + wpinitial;
    let wpbasic = max(6, 3 + mag(T), mag(aux2 * (26.0 + 2.0 * T)) + aux3);
    let wptheta = max(4, mag(2.04 * aux2) + aux3);
    let wpR = mag(4.0 * aux1) + aux3;
    w.set_prec(wptheta);
    let theta = siegeltheta(w);
    s.set_prec(wpR);
    let (xrz, yrz) = Rzeta_simul(s, k);
    w.set_prec(wpR);
    let pta = Complex::with_val(wpR, (0.25, 0.5)) * w;
    let ptb = Complex::with_val(wpR, (0.25, -0.5)) * w;
    let ps1;
    let ps2;
    let ps3;
    let ps4;
    if k > 0 { 
        ps1 = 0.25*(psi(0, pta) + psi(0, ptb)) - self.pi.ln()/2;
    }
    if k > 1 {
        ps2 = (Complex::with_val(wpR, (0.0, 1.0))/8.0) * (psi(1, pta) - psi(1, ptb));
    }
    if k > 2 {
        ps3 = (-1.0/16.0) * (psi(2, pta) + psi(2, ptb));
    }
    if k > 3 {
        ps4 = (Complex::with_val(wpR, (0.0, -1.0))/32.0) * (psi(3, pta) - psi(3, ptb));
    }
    theta.set_prec(wpbasic);
    let exptheta = mpc_expj(theta);
    let mut zv;
    j = Complex::with_val(wpbasic, (0.0, 1.0));
    if k == 0 {
        zv = exptheta * xrz[0] + yrz[0] / exptheta;
    } else if k == 1 {
        zv = j * exptheta * (xrz[1] + xrz[0] * ps1) - j * (yrz[1] + yrz[0] * ps1) / exptheta;
    } else if k == 2 {
        zv = exptheta * (-2 * xrz[1] * ps1 - xrz[0] * Pow::pow(ps1, 2) - xrz[2] + j * xrz[0] * ps2);
        zv = zv + (-2 * yrz[1] * ps1 - yrz[0] * Pow::pow(ps1, 2) - yrz[2] - j * yrz[0] * ps2) / exptheta;
    } else if k == 3 {
        let mut zv1 = -3 * xrz[1] * Pow::pow(ps1, 2) - xrz[0] * Pow::pow(ps1, 3) - 3 * xrz[2] * ps1 + j * 3 * xrz[1] * ps2;
        zv1 = (zv1 + 3*j * xrz[0] * ps1 * ps2 - xrz[3] + xrz[0] * ps3) * j * exptheta;
        let mut zv2 = 3 * yrz[1] * Pow::pow(ps1, 2) + yrz[0] * Pow::pow(ps1, 3) + 3 * yrz[2]* ps1 + j * 3 * yrz[1] * ps2;
        zv2 = j * (zv2 + 3*j * yrz[0] * ps1 * ps2 + yrz[3] - yrz[0] * ps3) / exptheta;
        zv = zv1 + zv2;
    } else if k == 4 {
        let mut zv1 = 4 * xrz[1] * Pow::pow(ps1, 3) + xrz[0] * Pow::pow(ps1, 4) + 6 * xrz[2] * Pow::pow(ps1, 2);
        zv1 = zv1 - 12*j * xrz[1] * ps1 * ps2 - 6*j * xrz[0] * Pow::pow(ps1, 2) * ps2 - 6*j * xrz[2] * ps2;
        zv1 = zv1 - 3 * xrz[0] * ps2 * ps2 + 4 * xrz[3] * ps1 - 4 * xrz[1] * ps3 - 4 * xrz[0] * ps1 * ps3;
        zv1 = zv1 + xrz[4] + j * xrz[0] * ps4;
        let mut zv2 = 4 * yrz[1] * Pow::pow(ps1, 3) + yrz[0] * Pow::pow(ps1, 4) + 6 * yrz[2] * Pow::pow(ps1, 2);
        zv2 = zv2 + 12*j * yrz[1] * ps1 * ps2 + 6*j * yrz[0] * Pow::pow(ps1, 2) * ps2 + 6*j * yrz[2] * ps2;
        zv2 = zv2 - 3 * yrz[0] * ps2 * ps2 + 4 * yrz[3] * ps1 - 4 * yrz[1] * ps3 - 4 * yrz[0] * ps1 * ps3;
        zv2 = zv2 + yrz[4] - j * yrz[0] * ps4;
        zv = exptheta * zv1 + zv2 / exptheta;
    }
    zv.set_prec(wpinitial);
    return zv;
}



fn rs_z(w, derivative: i32) {
    return z_offline(w, derivative);
}
