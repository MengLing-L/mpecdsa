/***********
 * This module implements a tagging system for Random Oracle queries (i.e. hash function calls)
 * Tags come in two flavors: dyadic tags, which are shared between pairs of parties and require no synchronization,
 * and broadcast tags, which are shared among arbitrary subsets of a large group of parties, operate in a single
 * source -> multiple destinations fashion, and require synchronization among the parties before they can be used.
 ***********/

use std::result::Result;
use std::sync::atomic::{AtomicU64, Ordering};

use rand::Rng;

use byteorder::{ByteOrder, LittleEndian};

use super::*;
use std::error::Error;

pub struct TagRange {
    base: Vec<u8>,
    counter: u64,
    length: u64,
}

pub struct GroupROTagger {
    playerindex: usize,
    puids: Vec<Vec<u8>>,
    subgroup_mask: Vec<bool>,
    subgroup_map_to_super: Vec<Option<usize>>,
    supergroup_map_to_sub: Vec<Option<usize>>,
    subgroup_size: usize,
    dyadic_bases: Vec<Vec<u8>>,
    dyadic_counters: Vec<AtomicU64>,
    broadcast_bases: Vec<Vec<u8>>,
    broadcast_counters: Vec<AtomicU64>,
}

pub struct DyadicROTagger<'a> {
    #[allow(dead_code)]
    playerindex: usize,
    counterparty: usize,
    dyadic_base: &'a [u8],
    dyadic_counter: &'a AtomicU64,
    counterparty_broadcast_base: &'a [u8],
    counterparty_broadcast_counter: &'a AtomicU64,
}

pub struct ModelessGroupROTagger<'a> {
    tagger: &'a GroupROTagger,
    is_dyadic: bool,
}

pub struct ModelessDyadicROTagger<'a, 'b> {
    tagger: &'a DyadicROTagger<'b>,
    is_dyadic: bool,
}

pub trait ROTagger {
    fn advance_counterparty_broadcast_counter(&self, a: usize, b: u64);
    fn next_counterparty_broadcast_tag(&self, a: usize) -> Vec<u8>;
    fn allocate_counterparty_broadcast_range(&self, counterparty: usize, length: u64) -> TagRange;

    fn advance_counterparty_dyadic_counter(&self, a: usize, b: u64);
    fn next_counterparty_dyadic_tag(&self, counterparty: usize) -> Vec<u8>;
    fn allocate_counterparty_dyadic_range(&self, counterparty: usize, length: u64) -> TagRange;
}

pub trait ModelessROTagger {
    fn next_tag(&self) -> Vec<u8>;
    fn allocate_range(&self, length: u64) -> TagRange;
    fn next_counterparty_tag(&self, a: usize) -> Vec<u8>;
    fn allocate_counterparty_range(&self, counterparty: usize, length: u64) -> TagRange;
}

// works over supergroup indices
fn party_broadcast_base(party: usize, puids: &[Vec<u8>], subgroup_mask: &[bool]) -> Vec<u8> {
    let mut hashin = vec![0u8; 8];
    LittleEndian::write_u64(&mut hashin[0..8], party as u64);
    for ii in 0..puids.len() {
        if subgroup_mask[ii] {
            hashin.extend_from_slice(&puids[ii]);
        }
    }
    let mut ro_out = vec![0u8; RO_TAG_SIZE];
    ro_out.copy_from_slice(&hash(&hashin)[0..RO_TAG_SIZE]);
    ro_out
}

impl GroupROTagger {
    // this constructor initializes all counters to 0 and does not allow anyone to complain - in practice, parties should be able to object to each others' counter values
    pub fn from_network_unverified<TR: Read, TW: Write, R: Rng>(
        playerindex: usize,
        rng: &mut R,
        recv: &mut [Option<&mut TR>],
        send: &mut [Option<&mut TW>],
    ) -> GroupROTagger {
        assert_eq!(recv.len(), send.len());

        let playercount = recv.len();
        let mut puid_seed = vec![0u8; playercount * HASH_SIZE];
        rng.fill_bytes(&mut puid_seed[(playerindex * HASH_SIZE)..((playerindex + 1) * HASH_SIZE)]);

        for ii in 0..playercount {
            if ii != playerindex {
                send[ii]
                    .as_mut()
                    .unwrap()
                    .write(&puid_seed[(playerindex * HASH_SIZE)..((playerindex + 1) * HASH_SIZE)])
                    .unwrap();
                send[ii].as_mut().unwrap().flush().unwrap();
            }
        }

        for ii in 0..playercount {
            if ii != playerindex {
                recv[ii]
                    .as_mut()
                    .unwrap()
                    .read_exact(&mut puid_seed[(ii * HASH_SIZE)..((ii + 1) * HASH_SIZE)])
                    .unwrap();
            }
        }

        Self::from_seed(
            playerindex,
            playercount,
            &mut puid_seed,
            &vec![true; playercount],
        )
    }

    // this constructor initializes all counters to 0 and does not allow anyone to complain - in practice, parties should be able to object to each others' counter values
    // note also that playerindex is given in supergroup indices!
    fn from_seed(
        playerindex: usize,
        playercount: usize,
        puid_seed: &[u8],
        subgroup_mask: &[bool],
    ) -> GroupROTagger {
        if subgroup_mask.len() != playercount {
            panic!();
        }
        assert!(
            subgroup_mask[playerindex],
            "Cannot apply subgroup mask that omits active party"
        );

        let mut ps = vec![0u8; puid_seed.len() + 8];
        let mut puids = vec![];

        ps[8..puid_seed.len() + 8].copy_from_slice(puid_seed);

        for ii in 0..playercount {
            LittleEndian::write_u64(&mut ps[0..8], ii as u64);
            puids.push(hash(&ps));
        }

        // each dyadic base is the hash of the uids of the two parties that share it, in numerical order
        let mut dyadic_bases = vec![vec![0u8; RO_TAG_SIZE]; playercount];

        // first calculate dyadic bases for pairings in which this party comes second
        for ii in 0..playerindex {
            dyadic_bases[ii] = hash(&[puids[ii].clone(), puids[playerindex].clone()].concat())
                [0..RO_TAG_SIZE]
                .to_vec();
        }
        // then calculate dyadic bases for pairings in which this party comes first
        for ii in playerindex + 1..playercount {
            dyadic_bases[ii] = hash(&[puids[playerindex].clone(), puids[ii].clone()].concat())
                [0..RO_TAG_SIZE]
                .to_vec();
        }

        // now, finally, the broadcast bases
        let mut broadcast_bases = vec![vec![0u8; RO_TAG_SIZE]; playercount];
        let mut subgroup_map_to_super = vec![None; playercount];
        let mut supergroup_map_to_sub = vec![None; playercount];
        let mut subgroup_size = 0;
        for ii in 0..playercount {
            if subgroup_mask[ii] {
                subgroup_map_to_super[subgroup_size] = Some(ii);
                supergroup_map_to_sub[ii] = Some(subgroup_size);
                broadcast_bases[ii] = party_broadcast_base(ii, &puids, subgroup_mask);
                subgroup_size += 1;
            }
        }

        // initialize all counters to 0. SEE NOTE AT FUNCTION HEADER.
        let mut dyadic_counters = Vec::with_capacity(playercount);
        let mut broadcast_counters = Vec::with_capacity(playercount);
        for _ in 0..playercount {
            dyadic_counters.push(AtomicU64::new(0));
            broadcast_counters.push(AtomicU64::new(0));
        }

        GroupROTagger {
            playerindex: playerindex,
            puids: puids,
            subgroup_mask: subgroup_mask.to_vec(),
            subgroup_map_to_super: subgroup_map_to_super,
            supergroup_map_to_sub: supergroup_map_to_sub,
            subgroup_size: subgroup_size,
            dyadic_bases: dyadic_bases,
            dyadic_counters: dyadic_counters,
            broadcast_bases: broadcast_bases,
            broadcast_counters: broadcast_counters,
        }
    }

    // Why not just implement Clone? We don't want people doing it accidentally. Cloning an ROTagger is not secure.
    // Note: this PANICS if any counters are locked! Use with extreme caution.
    pub fn unsafe_clone(&self) -> GroupROTagger {
        let mut dyadic_counters_cloned = Vec::with_capacity(self.puids.len());
        let mut broadcast_counters_cloned = Vec::with_capacity(self.puids.len());
        for ii in 0..self.puids.len() {
            dyadic_counters_cloned.push(AtomicU64::new(
                self.dyadic_counters[ii].load(Ordering::Relaxed),
            ));
            broadcast_counters_cloned.push(AtomicU64::new(
                self.broadcast_counters[ii].load(Ordering::Relaxed),
            ));
        }

        GroupROTagger {
            playerindex: self.playerindex,
            puids: self.puids.clone(),
            subgroup_mask: self.subgroup_mask.clone(),
            subgroup_map_to_super: self.subgroup_map_to_super.clone(),
            supergroup_map_to_sub: self.supergroup_map_to_sub.clone(),
            subgroup_size: self.subgroup_size,
            dyadic_bases: self.dyadic_bases.clone(),
            dyadic_counters: dyadic_counters_cloned,
            broadcast_bases: self.broadcast_bases.clone(),
            broadcast_counters: broadcast_counters_cloned,
        }
    }

    pub fn apply_subgroup_mask(&mut self, new_mask: &[bool]) -> Result<(), Box<dyn Error>> {
        if new_mask.len() != self.puids.len() {
            panic!();
        }
        if new_mask == &self.subgroup_mask[..] {
            return Ok(());
        }

        let mut subgroup_size = 0;
        for ii in 0..new_mask.len() {
            if new_mask[ii] {
                self.subgroup_map_to_super[subgroup_size] = Some(ii);
                self.supergroup_map_to_sub[ii] = Some(subgroup_size);
                self.broadcast_bases[ii] = party_broadcast_base(ii, &self.puids, new_mask);
                subgroup_size += 1;
            } else {
                self.supergroup_map_to_sub[ii] = None;
            }
        }
        for ii in subgroup_size..new_mask.len() {
            self.subgroup_map_to_super[ii] = None;
        }

        self.subgroup_size = subgroup_size;
        self.subgroup_mask = new_mask.to_vec();
        Ok(())
    }

    pub fn apply_subgroup_list(&mut self, list: &[usize]) -> Result<(), Box<dyn Error>> {
        if list.len() > self.puids.len() {
            panic!();
        }
        let mut mask = vec![false; self.puids.len()];
        for user in list {
            assert!(*user < mask.len(), "Subgroup list contains invalid user");
            mask[*user] = true;
        }
        self.apply_subgroup_mask(&mask)
    }

    pub fn remove_subgroup_mask(&mut self) {
        self.apply_subgroup_mask(&vec![true; self.puids.len()])
            .unwrap();
    }

    pub fn get_subgroup_party_count(&self) -> usize {
        self.subgroup_size
    }

    pub fn get_supergroup_party_count(&self) -> usize {
        self.puids.len()
    }

    pub fn current_broadcast_counter(&self) -> u64 {
        self.broadcast_counters[self.playerindex].load(Ordering::Relaxed)
    }

    pub fn advance_broadcast_counter(&self, tagindex: u64) {
        self.advance_counterparty_broadcast_counter(
            self.supergroup_map_to_sub[self.playerindex].unwrap(),
            tagindex,
        )
    }

    pub fn next_broadcast_tag(&self) -> Vec<u8> {
        self.next_counterparty_broadcast_tag(self.supergroup_map_to_sub[self.playerindex].unwrap())
    }

    pub fn allocate_broadcast_range(&self, length: u64) -> TagRange {
        self.allocate_counterparty_broadcast_range(
            self.supergroup_map_to_sub[self.playerindex].unwrap(),
            length,
        )
    }

    pub fn fork_tagger(&self) -> GroupROTagger {
        self.fork_counterparty_tagger(self.supergroup_map_to_sub[self.playerindex].unwrap())
    }

    pub fn fork_counterparty_tagger(&self, counterparty: usize) -> GroupROTagger {
        // implicitly uses subgroup indices
        let tag = self.next_counterparty_broadcast_tag(counterparty);
        Self::from_seed(
            self.playerindex,
            self.puids.len(),
            &tag[..],
            &self.subgroup_mask,
        )
    }

    pub fn get_dyadic_tagger<'a>(&'a self, counterparty: usize) -> DyadicROTagger<'a> {
        let supercounterparty = self.subgroup_map_to_super[counterparty].unwrap();
        //if supercounterparty == self.playerindex {panic!();}
        DyadicROTagger {
            playerindex: self.supergroup_map_to_sub[self.playerindex].unwrap(),
            counterparty: counterparty, // uses subgroup indices
            dyadic_base: &self.dyadic_bases[supercounterparty],
            dyadic_counter: &self.dyadic_counters[supercounterparty],
            counterparty_broadcast_base: &self.broadcast_bases[supercounterparty],
            counterparty_broadcast_counter: &self.broadcast_counters[supercounterparty],
        }
    }
}

impl ROTagger for GroupROTagger {
    fn advance_counterparty_broadcast_counter(&self, counterparty: usize, tagindex: u64) {
        let supercounterparty = self.subgroup_map_to_super[counterparty].unwrap();
        let oldcounter =
            self.broadcast_counters[supercounterparty].fetch_max(tagindex, Ordering::Relaxed);

        assert!(
            oldcounter <= tagindex,
            "Party {}/{} (subgroup/supergroup) attempted to reuse Random Oracle tag",
            counterparty,
            supercounterparty
        );
    }

    fn next_counterparty_broadcast_tag(&self, counterparty: usize) -> Vec<u8> {
        let supercounterparty = self.subgroup_map_to_super[counterparty].unwrap();
        let oldcounter = self.broadcast_counters[supercounterparty].fetch_add(1, Ordering::Relaxed);
        let mut ro_out = self.broadcast_bases[supercounterparty].clone();
        let temp = LittleEndian::read_u64(&ro_out[0..8]).wrapping_add(oldcounter);
        LittleEndian::write_u64(&mut ro_out[0..8], temp);
        ro_out
    }

    fn allocate_counterparty_broadcast_range(&self, counterparty: usize, length: u64) -> TagRange {
        let supercounterparty = self.subgroup_map_to_super[counterparty].unwrap();
        let mut base = self.broadcast_bases[supercounterparty].clone();
        let oldcounter =
            self.broadcast_counters[supercounterparty].fetch_add(length, Ordering::Relaxed);
        TagRange {
            base: base,
            counter: oldcounter,
            length: oldcounter + length,
        }
    }

    fn advance_counterparty_dyadic_counter(&self, counterparty: usize, tagindex: u64) {
        let supercounterparty = self.subgroup_map_to_super[counterparty].unwrap();
        let oldcounter =
            self.dyadic_counters[supercounterparty].fetch_max(tagindex, Ordering::Relaxed);
        assert!(
            oldcounter <= tagindex,
            "Party {}/{} (subgroup/supergroup) attempted to reuse Random Oracle tag",
            counterparty,
            supercounterparty
        );
    }

    fn next_counterparty_dyadic_tag(&self, counterparty: usize) -> Vec<u8> {
        let supercounterparty = self.subgroup_map_to_super[counterparty].unwrap();
        let oldcounter = self.dyadic_counters[supercounterparty].fetch_add(1, Ordering::Relaxed);
        let mut ro_out = self.dyadic_bases[supercounterparty].clone();
        let temp = LittleEndian::read_u64(&ro_out[0..8]).wrapping_add(oldcounter);
        LittleEndian::write_u64(&mut ro_out[0..8], temp);
        ro_out
    }

    fn allocate_counterparty_dyadic_range(&self, counterparty: usize, length: u64) -> TagRange {
        let supercounterparty = self.subgroup_map_to_super[counterparty].unwrap();
        let mut base = vec![0u8; RO_TAG_SIZE];
        base.copy_from_slice(&self.dyadic_bases[supercounterparty]);
        let oldcounter =
            self.dyadic_counters[supercounterparty].fetch_add(length, Ordering::Relaxed);
        TagRange {
            base: base,
            counter: oldcounter,
            length: oldcounter + length,
        }
    }
}

impl<'a> ModelessGroupROTagger<'a> {
    pub fn new(grot: &GroupROTagger, is_dyadic: bool) -> ModelessGroupROTagger {
        ModelessGroupROTagger {
            tagger: grot,
            is_dyadic: is_dyadic,
        }
    }
}

impl<'a> ModelessROTagger for ModelessGroupROTagger<'a> {
    fn next_tag(&self) -> Vec<u8> {
        assert!(
            !self.is_dyadic,
            "Tried to generate dyadic tag with no defined counterparty"
        );
        self.tagger.next_broadcast_tag()
    }

    fn allocate_range(&self, length: u64) -> TagRange {
        assert!(
            !self.is_dyadic,
            "Tried to allocate dyadic tag range with no defined counterparty"
        );
        self.tagger.allocate_broadcast_range(length)
    }

    fn next_counterparty_tag(&self, counterparty: usize) -> Vec<u8> {
        if self.is_dyadic {
            self.tagger.next_counterparty_dyadic_tag(counterparty)
        } else {
            self.tagger.next_counterparty_broadcast_tag(counterparty)
        }
    }

    fn allocate_counterparty_range(&self, counterparty: usize, length: u64) -> TagRange {
        if self.is_dyadic {
            self.tagger
                .allocate_counterparty_dyadic_range(counterparty, length)
        } else {
            self.tagger
                .allocate_counterparty_broadcast_range(counterparty, length)
        }
    }
}

impl<'a> DyadicROTagger<'a> {
    pub fn next_dyadic_tag(&self) -> Vec<u8> {
        self.next_counterparty_dyadic_tag(self.counterparty)
    }

    pub fn allocate_dyadic_range(&self, length: u64) -> TagRange {
        self.allocate_counterparty_dyadic_range(self.counterparty, length)
    }

    pub fn next_dyadic_counterparty_broadcast_tag(&self) -> Vec<u8> {
        self.next_counterparty_broadcast_tag(self.counterparty)
    }

    pub fn allocate_dyadic_counterparty_broadcast_range(&self, length: u64) -> TagRange {
        self.allocate_counterparty_broadcast_range(self.counterparty, length)
    }
}

impl<'a> ROTagger for DyadicROTagger<'a> {
    fn advance_counterparty_broadcast_counter(&self, counterparty: usize, tagindex: u64) {
        assert_eq!(
            self.counterparty, counterparty,
            "Attempted to advance broadcast RO counter for non-designated counterparty"
        );
        let oldcounter = self
            .counterparty_broadcast_counter
            .fetch_max(tagindex, Ordering::Relaxed);
        assert!(
            oldcounter <= tagindex,
            "Party {} attempted to reuse Random Oracle tag",
            counterparty
        );
    }

    fn next_counterparty_broadcast_tag(&self, counterparty: usize) -> Vec<u8> {
        assert_eq!(
            self.counterparty, counterparty,
            "Attempted to generate broadcast RO tag for non-designated counterparty"
        );
        let oldcounter = self
            .counterparty_broadcast_counter
            .fetch_add(1, Ordering::Relaxed);
        let mut ro_out = self.counterparty_broadcast_base.to_vec();
        let temp = LittleEndian::read_u64(&ro_out[0..8]).wrapping_add(oldcounter);
        LittleEndian::write_u64(&mut ro_out[0..8], temp);
        ro_out
    }

    fn allocate_counterparty_broadcast_range(&self, counterparty: usize, length: u64) -> TagRange {
        assert_eq!(
            self.counterparty, counterparty,
            "Attempted to allocate broadcast RO tag range for non-designated counterparty"
        );
        let oldcounter = self
            .counterparty_broadcast_counter
            .fetch_add(length, Ordering::Relaxed);
        let mut base = self.counterparty_broadcast_base.to_vec();
        TagRange {
            base: base,
            counter: oldcounter,
            length: length + oldcounter,
        }
    }

    fn advance_counterparty_dyadic_counter(&self, counterparty: usize, tagindex: u64) {
        assert_eq!(
            self.counterparty, counterparty,
            "Attempted to advance dyadic RO counter for non-designated counterparty."
        );
        let oldcounter = self.dyadic_counter.fetch_max(tagindex, Ordering::Relaxed);
        assert!(
            oldcounter <= tagindex,
            "Party {} attempted to reuse Random Oracle tag",
            counterparty
        );
    }

    fn next_counterparty_dyadic_tag(&self, counterparty: usize) -> Vec<u8> {
        assert_eq!(
            self.counterparty, counterparty,
            "Attempted to generate dyadic RO tag for non-designated counterparty."
        );
        let oldcounter = self.dyadic_counter.fetch_add(1, Ordering::Relaxed);
        let mut ro_out = self.dyadic_base.to_vec();
        let temp = LittleEndian::read_u64(&ro_out[0..8]).wrapping_add(oldcounter);
        LittleEndian::write_u64(&mut ro_out[0..8], temp);
        ro_out
    }

    fn allocate_counterparty_dyadic_range(&self, counterparty: usize, length: u64) -> TagRange {
        assert_eq!(
            self.counterparty, counterparty,
            "Attempted to allocate dyadic RO tag range for non-designated counterparty."
        );
        let oldcounter = self.dyadic_counter.fetch_add(length, Ordering::Relaxed);
        let mut base = self.dyadic_base.to_vec();
        TagRange {
            base: base,
            counter: oldcounter,
            length: length + oldcounter,
        }
    }
}

impl<'a, 'b> ModelessDyadicROTagger<'a, 'b> {
    pub fn new(drot: &'a DyadicROTagger<'b>, is_dyadic: bool) -> Self {
        ModelessDyadicROTagger {
            tagger: drot,
            is_dyadic: is_dyadic,
        }
    }

    pub fn next_dyadic_counterparty_tag(&self) -> Vec<u8> {
        self.next_counterparty_tag(self.tagger.counterparty)
    }

    pub fn allocate_dyadic_counterparty_range(&self, length: u64) -> TagRange {
        self.allocate_counterparty_range(self.tagger.counterparty, length)
    }
}

impl<'a, 'b> ModelessROTagger for ModelessDyadicROTagger<'a, 'b> {
    fn next_tag(&self) -> Vec<u8> {
        assert!(
            self.is_dyadic,
            "Tried to autogenerate broadcast tags from dyadic tagger."
        );
        self.tagger.next_dyadic_tag()
    }

    fn allocate_range(&self, length: u64) -> TagRange {
        assert!(
            self.is_dyadic,
            "Tried to autogenerate broadcast tags from dyadic tagger."
        );
        self.tagger.allocate_dyadic_range(length)
    }

    fn next_counterparty_tag(&self, counterparty: usize) -> Vec<u8> {
        if self.is_dyadic {
            self.tagger.next_counterparty_dyadic_tag(counterparty)
        } else {
            self.tagger.next_counterparty_broadcast_tag(counterparty)
        }
    }

    fn allocate_counterparty_range(&self, counterparty: usize, length: u64) -> TagRange {
        if self.is_dyadic {
            self.tagger
                .allocate_counterparty_dyadic_range(counterparty, length)
        } else {
            self.tagger
                .allocate_counterparty_broadcast_range(counterparty, length)
        }
    }
}

impl TagRange {
    pub fn next(&mut self) -> Result<Vec<u8>, Box<dyn Error>> {
        assert!(self.counter < self.length);
        let mut ro_out = vec![0u8; RO_TAG_SIZE];
        ro_out.copy_from_slice(&self.base);
        let temp = LittleEndian::read_u64(&ro_out[0..8]).wrapping_add(self.counter);
        LittleEndian::write_u64(&mut ro_out[0..8], temp);
        self.counter += 1;
        Ok(ro_out)
    }
}
