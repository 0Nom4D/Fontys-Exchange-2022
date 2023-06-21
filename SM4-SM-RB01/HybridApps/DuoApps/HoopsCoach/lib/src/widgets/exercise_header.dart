import 'package:flutter/material.dart';

class ExerciseHeader extends StatelessWidget {
  const ExerciseHeader({super.key});

  @override
  Widget build(BuildContext context) {
    return Row(
      children: [
        SizedBox(
          height: MediaQuery.of(context).size.height * .25,
          width: MediaQuery.of(context).size.width * .511,
          child: Column(
            children: const [
              Text(
                "Evaluate your shooting proficiency and endurance for every spot on the court",
                textAlign: TextAlign.start,
                style: TextStyle(
                  color: Colors.white,
                  fontSize: 15,
                ),
              ),
            ]
          )
        ),
        Transform.translate(
          offset: Offset(MediaQuery.of(context).size.width * .05, -1 * (MediaQuery.of(context).size.height * .1)),
          child: Image.asset("assets/basketball_net.png")
        )
      ],
    );
  }
}