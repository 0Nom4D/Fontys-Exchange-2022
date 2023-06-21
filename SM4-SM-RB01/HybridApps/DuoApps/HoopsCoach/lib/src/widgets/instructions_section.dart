import 'package:flutter/material.dart';

class InstructionSection extends StatelessWidget {
  const InstructionSection({super.key});

  @override
  Widget build(BuildContext context) {
    return Padding(
      padding: const EdgeInsets.all(8.0),
      child: Column(
        crossAxisAlignment: CrossAxisAlignment.start,
        children: const [
          Text(
            "Instructions",
            textAlign: TextAlign.left,
            style: TextStyle(
              color: Colors.white,
              fontSize: 25,
              fontWeight: FontWeight.bold
            ),
          ),
          Padding(
            padding: EdgeInsets.only(left: 20.0),
            child: Text(
              """
• Stand on the Free-Throw / Foul Line (15 Feet)
• Place your shooting foot in line with the center of the rim
• Angle your body so your dominant side is closer to the hoop
""",
              textAlign: TextAlign.left,
              style: TextStyle(
                  color: Colors.white,
                  fontSize: 15,
              ),
            ),
          ),
        ],
      ),
    );
  }
}
