class Dog:
    def __init__(self, name):
        self.name = name

    def respond_to_command(self, command):
        if command == self.name: self.speak()

    def speak(self):
        print("bark bark!!")


fido = Dog("fido")
fido.respond_to_command("spot")  # does nothing
fido.respond_to_command("fido")  # prints bark bark
