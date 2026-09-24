use std::ops::Mul;
use ark_bn254::{Fr, G1Affine, G1Projective};
use ark_ec::CurveGroup;
use ark_ff::{UniformRand, Zero};
use rand::Rng;
use crate::dre::N;

/// Sample n G1 points ρ₀, ρ₁, ..., ρ_{n-1} satisfying:
///   ∑_{i=0}^{n-1} 2^i · ρ_i = O  (point at infinity)
pub fn sample_rhos<R: Rng>(rng: &mut R) -> Vec<G1Affine> {
    // Sample ρ₁, ..., ρ_{n-1} uniformly at random
    let rho_tail: Vec<G1Projective> = (1..N)
        .map(|_| G1Projective::rand(rng))
        .collect();

    // ρ₀ = -∑_{i=1}^{n-1} 2^i · ρ_i
    let mut rho_0 = G1Projective::zero();
    let mut power = Fr::from(2u64);
    for rho_i in &rho_tail {
        rho_0 += rho_i.mul(power);
        power *= Fr::from(2u64);
    }
    rho_0 = -rho_0;

    let mut rho = Vec::with_capacity(N);
    rho.push(rho_0);
    rho.extend(rho_tail);

    G1Projective::normalize_batch(&rho)
}

#[cfg(test)]
mod tests {
    use std::ops::Mul;
    use ark_bn254::{Fr, G1Projective};
    use ark_ff::Zero;
    use rand::thread_rng;
    use crate::dre::N;
    use crate::dre::utils::sample_rhos;

    #[test]
    fn test_sample_rho() {

        let mut rng = thread_rng();
        let rho = sample_rhos(&mut rng);

        assert_eq!(rho.len(), N);

        // Verify: ∑ 2^i · ρ_i = O
        let mut sum = G1Projective::zero();
        let mut power = Fr::from(1u64);
        for rho_i in &rho {
            sum += G1Projective::from(*rho_i).mul(power);
            power *= Fr::from(2u64);
        }

        assert!(sum.is_zero(), "constraint ∑ 2^i·ρ_i = O not satisfied");
    }
}
