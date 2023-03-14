use std::cell::RefCell;
use std::cmp::Ordering;
use std::ops::{Add, Deref, Mul, Neg};
use std::rc::Rc;

#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum Color {
    Red,
    Black
}
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum LR {
    L,
    R
}
#[derive(Debug,Clone,Copy,PartialEq,Eq)]
pub enum Balance {
    Pre,
    Fix,
    None
}
impl Neg for Color {
    type Output = Color;
    fn neg(self) -> Self::Output {
        match self {
            Color::Red => Color::Black,
            Color::Black => Color::Red
        }
    }
}
#[derive(Debug)]
pub struct KDNode<const D:usize,P,T> where P: PartialOrd + Mul + Add {
    positions:Rc<[P;D]>,
    value:Rc<RefCell<T>>,
    color: Rc<RefCell<Color>>,
    left:Option<Box<KDNode<D,P,T>>>,
    right:Option<Box<KDNode<D,P,T>>>,
}
impl<const D:usize,P,T> KDNode<D,P,T> where P: PartialOrd + Mul + Add {
    pub fn new(positions:Rc<[P;D]>,value:Rc<RefCell<T>>) -> KDNode<D,P,T> {
        KDNode {
            positions: positions,
            value: value,
            color: Rc::new(RefCell::new(Color::Red)),
            left: None,
            right: None,
        }
    }

    pub fn right_rotate(t: KDNode<D,P,T>) -> KDNode<D,P,T> {
        match t.left {
            Some(left) => {
                KDNode {
                    positions: left.positions,
                    value: left.value,
                    color: left.color,
                    left: left.left,
                    right: Some(Box::new(KDNode {
                        positions: t.positions,
                        value: t.value,
                        color: t.color,
                        left: left.right,
                        right: t.right,
                    }))
                }
            },
            None => t
        }
    }

    pub fn left_rotate(t: KDNode<D,P,T>) -> KDNode<D,P,T> {
        match t.right {
            Some(right) => {
                KDNode {
                    positions: right.positions,
                    value: right.value,
                    color: right.color,
                    right: right.right,
                    left: Some(Box::new(KDNode {
                        positions: t.positions,
                        value: t.value,
                        color: t.color,
                        right: right.left,
                        left: t.left,
                    }))
                }
            },
            None => t
        }
    }

    #[allow(dead_code)]
    fn left_and_right_rotate(mut t: KDNode<D,P,T>) -> KDNode<D,P,T> {
        match t.left.take() {
            None => {
                t
            },
            Some(left) => {
                t.left = Some(Box::new(Self::left_rotate(*left)));
                Self::right_rotate(t)
            }
        }
    }

    #[allow(dead_code)]
    fn right_and_left_rotate(mut t: KDNode<D,P,T>) -> KDNode<D,P,T> {
        match t.right.take() {
            None => {
                t
            },
            Some(right) => {
                t.right = Some(Box::new(Self::right_rotate(*right)));
                Self::left_rotate(t)
            }
        }
    }

    fn insert(t: Option<Box<KDNode<D,P,T>>>,
              positions:&Rc<[P;D]>,
              parent_color:Option<Color>,
              lr:Option<LR>,
              value:Rc<RefCell<T>>,
              demension:usize) -> (KDNode<D,P,T>,Balance) {
        match t {
            None if demension == D - 1 => {
                let b = if parent_color.map(|c| c == Color::Red).unwrap_or(false) {
                    Balance::Pre
                } else {
                    Balance::None
                };

                (KDNode::new(Rc::clone(positions), Rc::clone(&value)),b)
            },
            None => {
                let (n,b) = Self::insert(None,
                                         positions,
                                         None,
                                         None,
                                         Rc::clone(&value), (demension+1) % D);

                let t = KDNode {
                    positions: Rc::clone(positions),
                    value: Rc::clone(&value),
                    color: Rc::new(RefCell::new(Color::Red)),
                    left: None,
                    right: Some(Box::new(n))
                };

                Self::balance(t,demension,b,None,None)
            },
            Some(mut t) if demension == D - 1 => {
                if positions[demension].partial_cmp(&t.positions[demension]).unwrap() == Ordering::Less {
                    let (n,b) = Self::insert(t.left,
                                             positions,
                                             Some(*t.color.deref().borrow()),
                                             Some(LR::L),
                                             value, (demension+1) % D);

                    t.left = Some(Box::new(n));

                    (*t,b)
                } else {
                    let (n,b) = Self::insert(t.right,
                                             positions,
                                             Some(*t.color.deref().borrow()),
                                             Some(LR::R),
                                             value, (demension+1) % D);

                    t.right = Some(Box::new(n));

                    (*t,b)
                }
            },
            Some(mut t) => {
                if positions[demension].partial_cmp(&t.positions[demension]).unwrap() == Ordering::Less {
                    let (n,b) = Self::insert(t.left,
                                             positions,
                                             parent_color,
                                             lr,
                                             value, (demension+1) % D);

                    t.left = Some(Box::new(n));

                    if demension == 0 {
                        Self::balance(*t, demension, b, lr,Some(LR::L))
                    } else {
                        (*t,b)
                    }
                } else {
                    let (n,b) = Self::insert(t.right,
                                             positions,
                                             parent_color,
                                             lr,
                                             value, (demension+1) % D);

                    t.right = Some(Box::new(n));

                    if demension == 0 {
                        Self::balance(*t, demension, b, lr,Some(LR::R))
                    } else {
                        (*t,b)
                    }
                }
            }
        }
    }

    fn balance(t: KDNode<D,P,T>,demension:usize,balance:Balance,parent_lr:Option<LR>,lr:Option<LR>) -> (KDNode<D,P,T>,Balance) {
        if demension > 0 {
            (t,balance)
        } else {
            match balance {
                Balance::None => (t, balance),
                Balance::Pre => {
                    let lr = lr.unwrap();
                    let parent_lr = parent_lr.unwrap();

                    let t = if parent_lr != lr && lr == LR::L {
                        Self::right_rotate(t)
                    } else if parent_lr != lr && lr == LR::R {
                        Self::left_rotate(t)
                    } else {
                        t
                    };

                    *t.color.borrow_mut() = Color::Black;

                    (t,Balance::Fix)
                },
                Balance::Fix => {
                    let lr = lr.unwrap();

                    let t = match lr {
                        LR::L => Self::right_rotate(t),
                        LR::R => Self::left_rotate(t)
                    };

                    (t,Balance::None)
                }
            }
        }
    }
}
#[derive(Debug)]
pub struct KDTree<const D:usize,P,T> where P: PartialOrd + Mul + Add {
    root: Option<Box<KDNode<D,P,T>>>
}
impl<const D:usize,P,T> KDTree<D,P,T> where P: PartialOrd + Mul + Add {
    pub fn new() -> KDTree<D,P,T> {
        KDTree {
            root: None
        }
    }

    pub fn insert(&mut self,positions:[P;D],value:T) {
        let (n,_) = KDNode::insert(self.root.take(),
                                   &Rc::new(positions),
                                   None,
                                   None,
                                   Rc::new(RefCell::new(value)),
                                   0);
        self.root = Some(Box::new(n));
    }
}


