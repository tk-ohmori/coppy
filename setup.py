from setuptools import setup, find_packages

setup(
    name='coppy',
    version="0.1",
    install_requires=[
        'JPype1'
    ],
    description="Constraint Programming in Python",
    author='Takane Ohmori',
    packages=find_packages(),
    include_package_data=True,
)