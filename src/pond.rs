use std::{
    collections::{HashMap, VecDeque},
    fs,
    path::{Path, PathBuf},
};

use kdl::KdlDocument;

#[derive(Debug, Clone)]
pub enum DependencySource {
    Path(PathBuf),
    Repository(String),
    Git(String),
}

#[derive(Debug, Clone)]
pub struct Dependency {
    pub name: String,
    pub source: DependencySource,
}

#[derive(Debug, Clone)]
pub struct Target {
    pub file: PathBuf,
    pub outpath: PathBuf,
    pub func: String,
}

#[derive(Debug, Clone)]
pub struct Pond {
    pub path: PathBuf,
    pub name: String,
    pub version: String,
    pub dependencies: Vec<Dependency>,
    pub targets: HashMap<String, Target>,
}

impl Pond {
    pub fn try_from_path(pond_path: &Path) -> Result<Self, String> {
        let pond_str = fs::read_to_string(pond_path).unwrap();
        let kdl: KdlDocument = pond_str.parse().expect("Error parsing pond.kdl");

        let pond_name = kdl
            .get_args("name")
            .first()
            .expect("Failed to find pond name")
            .as_string()
            .unwrap()
            .to_string();
        let version = kdl
            .get_args("name")
            .first()
            .expect("Failed to find pond version")
            .as_string()
            .unwrap()
            .to_string();

        let mut dependencies = Vec::new();
        let deps = kdl.get("dependencies");
        if let Some(deps_node) = deps {
            let deps_children = deps_node.children();
            if let Some(deps_children) = deps_children {
                for dep in deps_children.nodes() {
                    let name = dep.name().value().to_string();
                    let path = dep.get("path");
                    let version = dep.entries()[0].value().as_string();
                    let git = dep.get("git");

                    let source = if let Some(path) = path {
                        let mut path = PathBuf::from(path.value().as_string().unwrap().to_string());
                        if path.is_relative() {
                            path = pond_path
                                .parent()
                                .unwrap()
                                .join(path)
                                .canonicalize()
                                .unwrap();
                        }

                        DependencySource::Path(path)
                    } else if let Some(version) = version {
                        DependencySource::Repository(version.to_string())
                    } else if let Some(git) = git {
                        DependencySource::Git(git.value().as_string().unwrap().to_string())
                    } else {
                        return Err(format!("Invalid dependency, {:?}", name));
                    };

                    dependencies.push(Dependency { name, source });
                }
            }
        }

        let mut targets = HashMap::new();
        let targs = kdl.get("targets");
        if let Some(targs_node) = targs {
            let targs_children = targs_node.children();
            if let Some(targs_children) = targs_children {
                for target in targs_children.nodes() {
                    let name = target.name().value().to_string();
                    let file = target.entries()[0]
                        .value()
                        .as_string()
                        .map(|f| {
                            let mut path = PathBuf::from(f);
                            if path.is_relative() {
                                path = pond_path.parent().unwrap().join(path)
                            }

                            path
                        })
                        .expect("No target file");

                    let func = target
                        .get("func")
                        .map(|f| f.value().as_string().unwrap().to_string())
                        .unwrap_or_else(|| "main".to_string());

                    let outpath = target
                        .get("outpath")
                        .map(|f| {
                            let mut path =
                                PathBuf::from(f.value().as_string().unwrap().to_string());
                            if path.is_relative() {
                                path = pond_path.parent().unwrap().join(path)
                            }

                            path
                        })
                        .unwrap_or_else(|| pond_path.parent().unwrap().join(format!("out")));

                    if targets.contains_key(&name) {
                        return Err(format!("Duplicate target {name}"));
                    }

                    targets.insert(
                        name,
                        Target {
                            file,
                            outpath,
                            func,
                        },
                    );
                }
            }
        }

        Ok(Pond {
            path: pond_path.to_path_buf(),
            name: pond_name,
            version,
            dependencies,
            targets,
        })
    }

    pub fn get_parent_path(&self) -> PathBuf {
        self.path.parent().unwrap().to_path_buf()
    }

    // TODO: what if theres another pond.kdl somewhere below this one?
    pub fn get_pond_files(&self) -> Result<Vec<PathBuf>, String> {
        let mut files = Vec::new();

        let mut dirs_to_check = VecDeque::new();
        dirs_to_check.push_back(self.get_parent_path().join("src"));

        while let Some(dir) = dirs_to_check.pop_front() {
            let paths = fs::read_dir(&dir).unwrap();
            for path in paths {
                let path = path.unwrap().path();

                if path.is_file() && path.extension().unwrap() == "fr" {
                    files.push(path);
                } else if path.is_dir() {
                    dirs_to_check.push_back(path);
                }
            }
        }

        Ok(files)
    }

    pub fn dependency_ponds(&self) -> Result<Vec<Pond>, String> {
        let mut ponds = Vec::new();

        for dep in &self.dependencies {
            match &dep.source {
                DependencySource::Repository(_) => todo!("Repository deps not supported yet"),
                DependencySource::Git(_) => todo!("Git deps not supported yet"),
                DependencySource::Path(path) => {
                    let full_path = self
                        .get_parent_path()
                        .join(path)
                        .canonicalize()
                        .expect("Invalid dep path");

                    let pond_path = find_pond_path(&full_path)?;
                    let pond = Pond::try_from_path(&pond_path)?;

                    let mut dependencies = pond.dependency_ponds()?;
                    for dep in &mut dependencies {
                        dep.name = format!("{}::{}", pond.name, dep.name);
                    }

                    ponds.append(&mut dependencies);
                    ponds.push(pond);
                }
            }
        }

        Ok(ponds)
    }
}

pub fn find_pond_path(path: &Path) -> Result<PathBuf, String> {
    let mut path = std::path::absolute(path).expect("Invalid path");

    if path.is_file() {
        path = path.parent().unwrap().to_path_buf();
    }

    let mut pond_path: Option<PathBuf> = None;
    while pond_path.is_none() {
        let paths = fs::read_dir(&path).unwrap();
        path = path.parent().expect("No pond.kdl").to_path_buf();
        for path in paths {
            let path = path.unwrap().path();
            if path.file_name().unwrap().to_str().unwrap() == "pond.kdl" {
                pond_path = Some(path);
                break;
            }
        }
    }

    Ok(pond_path.unwrap())
}
