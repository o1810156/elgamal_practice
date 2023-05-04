use dialoguer::{Input, console::Term, theme::ColorfulTheme, Select};
use elgamal_practice::elgamal::*;
use rand::prelude::*;
use rand_chacha::ChaChaRng;
use anyhow::{anyhow, Result};

#[allow(unused)]
fn naive_prime_judge(n: u64) -> bool {
    if n <= 1 {
        return false;
    }
    for i in 2..n {
        if i * i > n {
            break;
        }
        if n % i == 0 {
            return false;
        }
    }
    true
}

fn encdec_mode() -> Result<()> {
    let input: String = Input::new()
        .with_prompt("Enter your message")
        .interact()?;

    let mut rng = ChaChaRng::from_entropy();
    let (pk, sk) = keygen_for_u8(&mut rng);

    /*
    // prime check
    if naive_prime_judge(pk.get_p()) {
        println!("p is prime");
    } else {
        println!("p is not prime");
    }
    */

    println!("Public key: {:?}", pk);
    println!("Secret key: {:?}", sk);
    let v = pk.enc_str(&input, &mut rng)
        .map_err(|_| anyhow!("Encryption failed"))?;
    let s = sk.dec_str(&v)
        .map_err(|_| anyhow!("Decryption failed"))?;
    println!("Encrypted: {}", display_cipvec(&v));
    println!("Decrypted: {:?}", s);

    Ok(())
}

fn homomorphic_mode() -> Result<()> {
    let m1: u64 = Input::new()
        .with_prompt("Enter m1")
        .interact()?;

    let m2: u64 = Input::new()
        .with_prompt("Enter m2")
        .interact()?;

    println!("plain: {} * {} = {}", m1, m2, m1 * m2);

    let mut rng = ChaChaRng::from_entropy();
    let (pk, sk) = keygen_for_u8(&mut rng);

    println!("Public key: {:?}", pk);
    println!("Secret key: {:?}", sk);

    let c1 = pk.encrypt(m1, &mut rng)
        .map_err(|_| anyhow!("Encryption failed"))?;
    let c2 = pk.encrypt(m2, &mut rng)
        .map_err(|_| anyhow!("Encryption failed"))?;
    println!("Encrypted m1: {}", c1);
    println!("Encrypted m2: {}", c2);

    let c3 = c1 * c2;

    println!("Encrypted m1 * m2: {}", c3);

    let dm1 = sk.decrypt(&c1);
    let dm2 = sk.decrypt(&c2);
    let m3 = sk.decrypt(&c3);

    println!("Decrypted m1: {:?}", dm1);
    println!("Decrypted m2: {:?}", dm2);
    println!("Decrypted m1 * m2: {:?}", m3);

    println!("check: {} == {}: {}", m1 * m2, m3, m1 * m2 == m3);

    Ok(())
}

fn main() -> Result<()> {
    let items = vec!["Enc Dec", "Homomorphic Mul Eval"];
    let selection = Select::with_theme(&ColorfulTheme::default())
        .with_prompt("Select mode")
        .default(0)
        .items(&items[..])
        .interact_on(&Term::stderr())?;

    match selection {
        0 => encdec_mode()?,
        1 => homomorphic_mode()?,
        _ => unreachable!(),
    }

    Ok(())
}
