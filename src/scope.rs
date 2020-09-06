use std::cell::RefCell;
use std::collections::{ HashMap, BTreeSet };

use crate::data::{ contains_var, into_parts, subst };


pub type Type = Vec<String>;
pub type Expr = Vec<String>;

pub type Signature = (Type, Option<Expr>);
pub type EqClass = BTreeSet<Expr>;


#[derive(Clone, Debug)]
pub struct Env(Vec<Frame>);

#[derive(Clone, Debug)]
pub struct Frame {
    items: HashMap<String, Signature>,

    equalities: RefCell<BTreeSet<BTreeSet<Expr>>>,
}

impl Env {
    pub fn new() -> Self {
        Env(vec![Frame::new()])
    }

    pub fn get_items(&self) -> HashMap<&str, &Signature> {
        let mut items = HashMap::new();

        for frame in &self.0 {
            for (name, sig) in frame.get_items().iter() {
                items.insert(name.as_ref(), sig);
            }
        }

        items
    }

    pub fn contains_item(&self, name: &str) -> bool {
        self.0.iter().any(|frame| frame.contains_item(name))
    }

    pub fn gen_fresh(&self, mut name: String) -> String {
        while self.contains_item(&name) {
            name += "`";
        }

        name
    }

    pub fn insert(&mut self, name: String, val: Signature) -> Option<Signature> {
        if self.contains_item(&name) {
            let fresh = self.gen_fresh(name.clone());

            for frame in &mut self.0 {
                frame.rename(&name, fresh.clone());
            }
        }

        self.0.last_mut().unwrap().insert(name, val)
    }

    pub fn remove(&mut self, name: &str) -> Option<Signature> {
        self.0.last_mut().unwrap().remove(name)
    }

    pub fn get(&self, name: &str) -> Option<&Signature> {
        for frame in &self.0 {
            let ret = frame.get(name);

            if ret.is_some() {
                return ret;
            }
        }

        None
    }

    pub fn get_mut(&mut self, name: &str) -> Option<&mut Signature> {
        for frame in &mut self.0 {
            let ret = frame.get_mut(name);

            if ret.is_some() {
                return ret;
            }
        }

        None
    }

    pub fn has_eq_class(&self, val: &Expr) -> bool {
        self.0.iter().any(|frame| frame.has_eq_class(val))
    }

    pub fn new_eq_class(&self, val: Expr) {
        self.0.last().unwrap().new_eq_class(val)
    }

    pub fn add_eq(&self, representant: &Expr, new_member: Expr) {
        let mut owner = None;

        {
            for frame in self.0.iter() {
                if frame.has_eq_class(representant) {
                    owner = Some(frame);

                    break;
                }
            }
        }

        if let Some(frame) = owner {
            frame.add_eq(representant, new_member)

        } else {
            panic!["no equality class with representant:\n{}\n", representant.join("\n")];
        }
    }

    pub fn reduce(&self, expr: &Expr) -> Option<Expr> {
        for frame in &self.0 {
            if let Some(ret) = frame.reduce(expr) {
                return Some(ret);
            }
        }

        None
    }
}

impl Frame {
    pub fn new() -> Self {
        Frame {
            items: HashMap::new(),
            equalities: RefCell::new(BTreeSet::new()),
        }
    }

    fn get_items(&self) -> &HashMap<String, Signature> {
        &self.items
    }

    fn contains_item(&self, name: &str) -> bool {
        self.items.contains_key(name)
    }

    fn insert(&mut self, name: String, val: Signature) -> Option<Signature> {
        self.items.insert(name, val)
    }

    fn rename(&mut self, old: &str, new: String) {
        if self.items.contains_key(old) {
            let old_val = self.items.remove(old).unwrap();

            self.items.insert(new.clone(), old_val);
        }

        for (ty, val) in self.items.values_mut() {
            subst(ty, old, new.clone());

            if let Some(ref mut val) = val {
                subst(val, old, new.clone());
            }
        }

        let mut new_equalities = BTreeSet::new();

        for eqs in self.equalities.borrow().iter() {
            let mut new_eqs = BTreeSet::new();

            for val in eqs {
                let mut new_val = val.to_vec();

                subst(&mut new_val, old, new.clone());

                new_eqs.insert(new_val);
            }

            new_equalities.insert(new_eqs);
        }

        *self.equalities.borrow_mut() = new_equalities;
    }

    fn remove(&mut self, name: &str) -> Option<Signature> {
        self.items.remove(name)
    }

    fn get(&self, name: &str) -> Option<&Signature> {
        self.items.get(name)
    }

    fn get_mut(&mut self, name: &str) -> Option<&mut Signature> {
        self.items.get_mut(name)
    }

    fn has_eq_class(&self, val: &Expr) -> bool {
        self.equalities.borrow().iter().any(|eqs| eqs.contains(val))
    }

    fn new_eq_class(&self, val: Expr) {
        self.equalities.borrow_mut().insert({
            let mut tmp = BTreeSet::new();

            tmp.insert(val);

            tmp
        });
    }

    fn add_eq(&self, representant: &Expr, new_member: Expr) {
        let mut family = None;

        {
            let eq_bor = self.equalities.borrow();

            for eqs in eq_bor.iter() {
                if eqs.contains(representant) {
                    family = Some(eqs.clone());

                    break;
                }
            }
        }

        if let Some(mut family) = family {
            self.equalities.borrow_mut().remove(&family);

            family.insert(new_member);

            self.equalities.borrow_mut().insert(family);

        } else {
            panic!["no equality class with representant:\n{}\n", representant.join("\n")];
        }
    }

    fn reduce(&self, expr: &Expr) -> Option<Expr> {
        for eqs in self.equalities.borrow().iter() {
            if eqs.contains(expr) {
                return eqs.first().cloned();
            }
        }

        None
    }
}